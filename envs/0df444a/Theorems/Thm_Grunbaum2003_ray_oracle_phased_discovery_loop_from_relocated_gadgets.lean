-- Prove2me | Theorems.Thm_Grunbaum2003_ray_oracle_phased_discovery_loop_from_relocated_gadgets
-- name    : Grunbaum2003.ray_oracle_phased_discovery_loop_from_relocated_gadgets
-- status  : Disproved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:53:54.911191+00:00
-- url     : https://prove2.me/theorems/bc541f98-b35a-49bc-8516-6a1586e2efcc
-- title:
--   Phased facet-discovery prefix program from relocated gadgets and frame Cramer step
-- statement:
--   Let $d \ge 2$ and let $P \subset \mathbb{R}^d$ be a $d$-polytope with $0 \in \operatorname{int} P$, accessed through a ray oracle. Given the compiled ray-machine gadgets together with the boundary frame extension and Cramer facet-normal identification theorem, there exists a uniform ray-machine program that executes the phased facet-discovery and vertex-certification trace $(S_s, C_s, q_s)_{s \le N}$ and produces the $n \times f_0(P)$ face-vertex incidence table prior to the final inclusion-table pass within $q_N$ oracle queries:
--
--   $$
--   \operatorname{queries}(c_{\mathrm{pre}}) \le q_N, \qquad c_{\mathrm{pre}}.\mathrm{tape}(\mathrm{fvBase} + a V + k) = \mathbf{1}_{v_k \in F_a}.
--   $$
--
--   This isolates the outer loop assembly once all relocated gadget compositions and the single-step boundary frame Cramer normal identification are established.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §5.5; Gritzmann–Klee–Westwater 1995, §5.2–5.5

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace Grunbaum2003

theorem ray_oracle_phased_discovery_loop_from_relocated_gadgets (d : ℕ) (hd : 2 ≤ d)
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
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
    (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
    (hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z)
    (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
    (hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (hFrameCramer : ∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x))
    (headerAndInclusionTableProgram : ℕ → ℕ → ℤ → ℤ → List RayInstruction)
    (secondQueryProgram firstMidpointProgram referenceWalkProgram : List RayInstruction) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          d + 1 ≤ faceCount P (d - 1) →
          ∀ (L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ),
            P = {x | ∀ i, L i x ≤ 1} →
            (∀ i, L i = 0 ∨
              ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
                Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1)) →
            (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
            ∀ (V : Finset (Fin d → ℝ))
              (N : ℕ)
              (S_seq : ℕ → Finset (Fin (faceCount P (d - 1))))
              (C_seq : ℕ → Finset (Fin d → ℝ))
              (q_seq : ℕ → ℕ),
              (V : Set (Fin d → ℝ)) = P.extremePoints ℝ →
              (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
              V.card = faceCount P 0 →
              C_seq 0 = ∅ →
              q_seq 0 ≤ d + 1 →
              (∀ s < N,
                (S_seq (s + 1) = S_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    v ∈ P ∧ v ∉ C_seq s ∧ C_seq (s + 1) = insert v (C_seq s) ∧
                    q_seq (s + 1) ≤ q_seq s + 1) ∨
                (C_seq (s + 1) = C_seq s ∧
                  ∃ v ∈ ({x : Fin d → ℝ | ∀ i ∈ S_seq s, L i x ≤ 1}).extremePoints ℝ,
                    oracle v ≠ v ∧
                    ∃ i_new : Fin (faceCount P (d - 1)),
                      L i_new (oracle v) = 1 ∧
                      S_seq (s + 1) = insert i_new (S_seq s) ∧
                      q_seq (s + 1) ≤ q_seq s +
                        (1 + (d - 1) * (2 * (faceCount P (d - 1) - (S_seq s).card) + 3)))) →
              {x : Fin d → ℝ | ∀ i ∈ S_seq N, L i x ≤ 1} = P →
              C_seq N = V →
              ∃ (n : ℕ) (e : Fin n ≃ PolytopeFace P)
                (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}})
                (pre : List RayInstruction) (t_pre : ℕ) (c_pre : RayConfiguration)
                (fvBase minBase : ℤ),
                program = pre ++
                  (headerAndInclusionTableProgram n (faceCount P 0) fvBase minBase).map
                    (relocateInst pre.length) ∧
                rayMachineRun program oracle t_pre
                  { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
                    some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) ∧
                c_pre.queries ≤ q_seq N ∧
                ∀ (a : Fin n) (k : Fin (faceCount P 0)),
                  c_pre.tape (fvBase + (a.val : ℤ) * ((faceCount P 0 : ℕ) : ℤ) + (k.val : ℤ)) =
                    if (vEnum k).val ∈ (e a).val then (1 : ℝ) else 0 := by sorry

end Grunbaum2003
