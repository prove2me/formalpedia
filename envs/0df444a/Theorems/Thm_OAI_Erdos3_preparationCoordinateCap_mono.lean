-- Prove2me | Theorems.Thm_OAI_Erdos3_preparationCoordinateCap_mono
-- name    : OAI.Erdos3.preparationCoordinateCap_mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:27:32.208277+00:00
-- url     : https://prove2.me/theorems/8d12e328-d1ba-4f14-b2e8-f708f372a695
-- title:
--   The preparation coordinate cap is monotone in its first and third arguments
-- statement:
--   Let $m,s,D,t,T$ be natural numbers with $m\le s$ and $t\le T$. Then `preparationCoordinateCap m D t` $\le$ `preparationCoordinateCap s D T`, where `preparationCoordinateCap s D T` is the natural number $D(T+1)^s+D+T+1$.
--
--   Lean: `OAI.Erdos3.preparationCoordinateCap_mono` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationCoordinateCap_mono {m s D t T : ℕ}
    (hms : m ≤ s) (htT : t ≤ T) :
    preparationCoordinateCap m D t ≤ preparationCoordinateCap s D T := by
  sorry

end Erdos3
end
end OAI
