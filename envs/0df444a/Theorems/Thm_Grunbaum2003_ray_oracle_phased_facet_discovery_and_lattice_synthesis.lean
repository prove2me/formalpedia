-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_phased_facet_discovery_and_lattice_synthesis
-- name    : Grunbaum2003.ray_oracle_phased_facet_discovery_and_lattice_synthesis
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T19:08:54.426099+00:00
-- url     : https://prove2.me/theorems/1e290640-7605-4a3d-b071-2fc9564e8e75
-- title:
--   Outer phased facet-discovery loop and face-lattice tape synthesis for Gritzmann–Klee–Westwater reconstruction ($d \ge 2$)
-- statement:
--   This theorem isolates the outer-loop assembly and final face-lattice tape encoding step of the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm in dimensions $d \ge 2$, given the already-proved machine and geometric components:
--   - program relocation (`relocateInst`, `relocateCfg`) and the $(d+9)$-step ambient planar-section query adapter from `rayMachine_relocate_and_section_query_adapter`;
--   - the $(d+1)$-query inner-simplex initialization program `innerSampleProgram d` from `rayMachine_inner_simplex_and_signed_direction_program`;
--   - the local sector slackness and known-facet exclusion bounds from `rayOracle_local_sector_and_known_facet_exclusion`;
--   - the boundary frame extension and Cramer facet-normal recovery `frameNormal` from `rayFrame_boundary_extension_axes_and_cramer_normal`;
--   - the planar reference-walk machine (`secondQueryProgram`, `firstMidpointProgram`, `referenceWalkProgram`) and one-sided secant query bound $2(m - k) + 3$ from `rayMachine_planar_reference_walk_and_one_sided_budget`; and
--   - the normalized facet halfspace presentation $P = \{x \in \mathbb{R}^d \mid \forall i \in \operatorname{Fin} m,\, L_i(x) \le 1\}$ with $m = f_{d-1}(P) \ge d + 1$ from `polytope_normalized_halfspace_presentation_and_facet_lower_bound`.
--
--   Under these inputs, there exists a uniform ray-machine program `program : List RayInstruction` that halts on every $d$-polytope $P \subseteq \mathbb{R}^d$ ($0 \in \operatorname{int}(P)$) and ray oracle `oracle` with `IsRayFaceLatticeOutput P c` and total query count bounded by the phased Gritzmann–Klee–Westwater sum
--   $$
--   c.\mathrm{queries} \le f_0(P) + (d + 1) + \sum_{k=0}^{f_{d-1}(P) - 1} \bigl(1 + (d - 1)\bigl(2(f_{d-1}(P) - k) + 3\bigr)\bigr).
--   $$
--   Combining this phased sum with `repaired_ray_query_budget_bound` immediately yields the closed-form query bound $f_0(P) + (d - 1) f_{d-1}(P)^2 + (5d - 4) f_{d-1}(P)$ of `ray_oracle_face_lattice_reconstruction_ge_two`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Analysis.Convex.Exposed
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix

namespace Grunbaum2003

theorem ray_oracle_phased_facet_discovery_and_lattice_synthesis (d : ℕ) (hd : 2 ≤ d)
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (innerSampleProgram : ℕ → List RayInstruction)
    (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ)
    (hInnerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
      ∃ c : RayConfiguration,
        rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
          {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
        c.pc = (d + 1) * (d + 2) + 2 ∧
        (innerSampleProgram d)[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = q + (d + 1) ∧
        (∀ i : Fin (d + 1), ∀ j : Fin d,
          c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
        (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z))
    (frameCramerCoefficients : Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
    (frameNormal : Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ)
    (hFrameNormal : ∀ (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
      frameNormal v x = ∑ k, frameCramerCoefficients v k * x k)
    (hLocalSlack : ∀ {k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M))
    (secondQueryProgram firstMidpointProgram referenceWalkProgram : List RayInstruction) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          d + 1 ≤ faceCount P (d - 1) →
          (∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
            P = {x | ∀ i, L i x ≤ 1} ∧
            ∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1)) →
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d + 1) +
              ∑ k ∈ Finset.range (faceCount P (d - 1)),
                (1 + (d - 1) * (2 * (faceCount P (d - 1) - k) + 3)) ∧
            IsRayFaceLatticeOutput P c := by sorry

end Grunbaum2003
