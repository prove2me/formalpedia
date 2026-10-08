-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarMesh_movement_bound
-- name    : OAI.Erdos3.scalarMesh_movement_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:45:41.223773+00:00
-- url     : https://prove2.me/theorems/80164751-a0ad-4a41-abf2-d39d7696235f
-- title:
--   1 + d(C+B) is at most exp(scalarMeshLog G P T)
-- statement:
--   Let $d,C,B,G,P,T$ be real numbers with $0\le C$, $0\le B$, $0\le G$, $0\le P$, $0\le T$, $d\le e^P$, $C\le e^P$ and $B\le e^P$ (no sign condition on $d$). Then
--   $$1+d\,(C+B)\le\exp\big(\texttt{scalarMeshLog}\ G\ P\ T\big),$$
--   where `scalarMeshLog G P T` is the real number $G+3P+T+50$.
--
--   Lean: `OAI.Erdos3.scalarMesh_movement_bound` in `lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean#L34

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem scalarMesh_movement_bound {d C B G P T : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdP : d ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hBP : B ≤ Real.exp P) :
    1 + d * (C + B) ≤ Real.exp (scalarMeshLog G P T) := by
  sorry

end Erdos3
end
end OAI
