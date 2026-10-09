-- Prove2me | Theorems.Thm_OAI_Erdos3_affineComparisonScale_count
-- name    : OAI.Erdos3.affineComparisonScale_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:13:19.895482+00:00
-- url     : https://prove2.me/theorems/d012f4e4-1600-49c6-b661-d401ad1a958b
-- title:
--   A cardinality bounded by e^C is bounded by e to the affine comparison scale
-- statement:
--   Let $\iota$ be a finite type, and let $\varepsilon, L, T, C$ be real numbers with $0 \le L$, $0 \le T$ and $0 \le C$. Suppose $|\iota| \le e^{C}$. Then $|\iota| \le \exp(\texttt{affineComparisonScale}\ \varepsilon\ L\ T\ C)$, where `affineComparisonScale ε L T C` $= L + T + 2 + (\texttt{affineRemovalDepth}\ T + \texttt{affineComparisonTail}\ \varepsilon\ L\ T) + C$ is OpenAI's real-valued scale (the middle summand being a sum of two natural numbers defined by OpenAI).
--
--   Lean: `OAI.Erdos3.affineComparisonScale_count` in `lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffinePrimitiveLogBudget.lean#L32

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_count {ι : Type*} [Fintype ι] {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C) :
    (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) := by
  sorry

end Erdos3
end
end OAI
