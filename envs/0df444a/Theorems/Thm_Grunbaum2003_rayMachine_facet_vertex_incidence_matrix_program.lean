-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_facet_vertex_incidence_matrix_program
-- name    : Grunbaum2003.rayMachine_facet_vertex_incidence_matrix_program
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:45:52.450137+00:00
-- url     : https://prove2.me/theorems/f1757593-1e91-4b57-a052-4cee97f761be
-- title:
--   Compiled ray-machine program emitting the complete $m \times V$ $0/1$ facet-vertex hyperplane incidence matrix
-- statement:
--   Given $m$ facet normals $L_0, \dots, L_{m-1} \in \mathbb{R}^d$ stored row-major at `lBase + j * d + i` and $V$ candidate vertices $x_0, \dots, x_{V-1} \in \mathbb{R}^d$ stored row-major at `xBase + k * d + i`, `facetVertexIncidenceMatrixProgram d m V lBase xBase minBase` evaluates all $m \cdot V$ affine slacks $\langle L_j, x_k \rangle - 1$ and applies the vectorized 2-step 3-way `.branch` zero-indicator `zeroIndicatorVec (m * V)` in-place, writing the complete $m \times V$ $0/1$ incidence matrix $I_{j, k} = [\langle L_j, x_k \rangle = 1]$ into `outBase + j * V + k` (`outBase ≥ minBase`) with `0` oracle queries while preserving all tape cells `< outBase`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem rayMachine_facet_vertex_incidence_matrix_program :
  ∃ (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ),
    ∀ {d m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
        (∀ z : ℤ, z < outBase → c'.tape z = source z) := by sorry

end Grunbaum2003
