-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarMeshLog_bounds
-- name    : OAI.Erdos3.scalarMeshLog_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:06:54.762014+00:00
-- url     : https://prove2.me/theorems/5385e294-223b-4352-a174-beec6631e9fd
-- title:
--   Lower bounds on scalarMeshLog G P T
-- statement:
--   Let $G,P,T$ be real numbers with $0\le G$, $0\le P$, $0\le T$, and write $S$ for `scalarMeshLog G P T`, the real number $G+3P+T+50$. Then $0\le S$, $P\le S$, $T\le S$, $G+3P+40\le S$, and $2P+3\le S$.
--
--   Lean: `OAI.Erdos3.scalarMeshLog_bounds` in `lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B009` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/ScalarMeshCoefficientBudget.lean#L12

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

namespace OAI

section

namespace Erdos3

theorem scalarMeshLog_bounds {G P T : ℝ} (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    0 ≤ scalarMeshLog G P T ∧ P ≤ scalarMeshLog G P T ∧ T ≤ scalarMeshLog G P T ∧
      G + 3 * P + 40 ≤ scalarMeshLog G P T ∧ 2 * P + 3 ≤ scalarMeshLog G P T := by
  sorry

end Erdos3
end
end OAI
