-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarMesh_boundary_bound
-- name    : OAI.Erdos3.scalarMesh_boundary_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:42:36.318813+00:00
-- url     : https://prove2.me/theorems/7df2aebd-6f81-473e-a994-44676b2201cb
-- title:
--   40nA/(ρc) is at most exp(scalarMeshLog G P T)
-- statement:
--   Let $n,A,\rho,c,G,P,T$ be real numbers with $0\le n$, $0\le A$, $0<\rho$, $0<c$, $0\le G$, $0\le P$, $0\le T$, $n\le e^P$, $A\le e^P$, $\rho^{-1}\le e^G$ and $c^{-1}\le e^P$. Then
--   $$\frac{40\,n\,A}{\rho\,c}\le \exp\big(\texttt{scalarMeshLog}\ G\ P\ T\big),$$
--   where `scalarMeshLog G P T` is the real number $G+3P+T+50$.
--
--   Lean: `OAI.Erdos3.scalarMesh_boundary_bound` in `lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean#L18

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem scalarMesh_boundary_bound {n A rho c G P T : ℝ}
    (hn : 0 ≤ n) (hA : 0 ≤ A) (hrho : 0 < rho) (hc : 0 < c)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hnP : n ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrhoG : rho⁻¹ ≤ Real.exp G) (hcP : c⁻¹ ≤ Real.exp P) :
    40 * n * A / (rho * c) ≤ Real.exp (scalarMeshLog G P T) := by
  sorry

end Erdos3
end
end OAI
