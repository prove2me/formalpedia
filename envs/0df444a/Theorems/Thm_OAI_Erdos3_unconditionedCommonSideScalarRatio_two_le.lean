-- Prove2me | Theorems.Thm_OAI_Erdos3_unconditionedCommonSideScalarRatio_two_le
-- name    : OAI.Erdos3.unconditionedCommonSideScalarRatio_two_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T02:03:27.726493+00:00
-- url     : https://prove2.me/theorems/8d9e53ec-47b2-4a97-bf3b-2b188cabd606
-- title:
--   The unconditioned common-side scalar ratio is at least 2
-- statement:
--   For every natural number $n \ge 1$, $2 \le$ `unconditionedCommonSideScalarRatio n`, where `unconditionedCommonSideScalarRatio n` is the natural number $1 + n \cdot$ `unconditionedScalarPrimeRatio n` and `unconditionedScalarPrimeRatio n` $= \lceil e^{n+2} \rceil + 2$.
--
--   Lean: `OAI.Erdos3.unconditionedCommonSideScalarRatio_two_le` in `lean/OAI/Combinatorics/Progressions/Estimates/UnconditionedCommonSideScalarRatioBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1328` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/UnconditionedCommonSideScalarRatioBounds.lean#L9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1328

namespace OAI

section

namespace Erdos3

theorem unconditionedCommonSideScalarRatio_two_le {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ unconditionedCommonSideScalarRatio n := by
  sorry

end Erdos3
end
end OAI
