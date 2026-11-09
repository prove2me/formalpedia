-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_perturbed_midpoint_cramer_and_incidence_composition
-- name    : Grunbaum2003.rayMachine_perturbed_midpoint_cramer_and_incidence_composition
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:31:39.595666+00:00
-- url     : https://prove2.me/theorems/549e0e4c-1613-446e-854c-29f3ae61c9b6
-- title:
--   Relocated Prefix Composition for Perturbed Queries, Midpoints, Cramer Facet Rows, and Incidence Matrices
-- statement:
--   Establishes the relocated prefix compositions for perturbedRayQueryProgram, midpointVecProgram, and facetVertexIncidenceMatrixProgram, and proves that cramerRowProgram on any rank-d boundary frame writes the exact coefficient vector of a fresh facet functional L i_new with i_new not in S and L i_new p0 = 1.
-- source:
--   Gritzmann, Klee, Westwater (1995), §5.2–5.5; Grünbaum, Convex Polytopes (2003)

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace Grunbaum2003

theorem rayMachine_perturbed_midpoint_cramer_and_incidence_composition (d : ℕ) :
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
       (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
       (_hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ),
      rayMachineRun (pre ++
          (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      (fun i : Fin d =>
        c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries + 1 ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              c_pre.tape (pBase + (j.val : ℤ)) +
                c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
       (S : Finset (Fin m)),
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
            ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) →
      ∀ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
        (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
        (cramerRowSteps : ℕ → ℤ → ℕ),
      (∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ)
        (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      ∀ (p p₀ : Fin d → ℝ),
        LinearIndependent ℝ
          (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ i : Fin d,
          (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P) →
        p ∈ frontier P →
        p = ∑ i : Fin d,
          w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ (c' : RayConfiguration) (i_new : Fin m),
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ x : Fin d → ℝ,
            ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
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
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) := by sorry

end Grunbaum2003
