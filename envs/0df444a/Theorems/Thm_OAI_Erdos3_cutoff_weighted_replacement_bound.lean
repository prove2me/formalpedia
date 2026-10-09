-- Prove2me | Theorems.Thm_OAI_Erdos3_cutoff_weighted_replacement_bound
-- name    : OAI.Erdos3.cutoff_weighted_replacement_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:48:59.303173+00:00
-- url     : https://prove2.me/theorems/d5c89291-5804-422d-9e48-838816eb3842
-- title:
--   The integer-box bad-pair budget at the replacement tolerance gives an epsilon error
-- statement:
--   Let $d$ and $R$ be natural numbers and $F, E, \varepsilon, C, M$ real numbers with $2 \le d$, $0 \le F$, $0 \le E$, $0 \le C$ and $0 < \varepsilon$. Write $\tau = $ `weightedReplacementTolerance F E ε` $= \min\bigl(1, \varepsilon^2 / (1 + F^2(1+E))\bigr)$. Suppose `integerBoxPairScale d C τ` $\le M$, where `integerBoxPairScale d C τ` $= \max\bigl(\texttt{integerBoxGcdCutoff}\ d\ C\ \tau,\ 1/\texttt{integerBoxNearRatio}\ d\ \tau\bigr)$ with `integerBoxGcdCutoff d C τ` $= \lceil 2 \cdot 2^{d-1}(1+C)/\tau \rceil + 1 \in \mathbb{N}$ and `integerBoxNearRatio d τ` $= \min\bigl(1, \tau/(1 + 2 \cdot 3^d)\bigr)$; and suppose $R \le C M$. Then
--   $$F \sqrt{E \cdot \beta + \tau} \le \varepsilon, \qquad \beta = \texttt{integerBoxBadPairBudget}\ d\ G\ R\ \bigl\lfloor \texttt{integerBoxNearRatio}\ d\ \tau \cdot M \bigr\rfloor\ M,$$
--   where $G = $ `integerBoxGcdCutoff d C τ`, the floor is the natural-number floor, and `integerBoxBadPairBudget d B R r L` $= 2^{d-1}\bigl(1/B^{d-1} + R/L^{d}\bigr) + \bigl((2r+1)/L\bigr)^{d}$ (with natural-number subtraction $d - 1$).
--
--   Lean: `OAI.Erdos3.cutoff_weighted_replacement_bound` in `lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean#L40

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem cutoff_weighted_replacement_bound (d R : ℕ) {F E epsilon C M : ℝ}
    (hd : 2 ≤ d) (hF : 0 ≤ F) (hE : 0 ≤ E) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C (weightedReplacementTolerance F E epsilon) ≤ M)
    (hR : (R : ℝ) ≤ C * M) :
    F * Real.sqrt (E * integerBoxBadPairBudget d
      (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon)) R
      ⌊integerBoxNearRatio d (weightedReplacementTolerance F E epsilon) * M⌋₊ M +
      weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  sorry

end Erdos3
end
end OAI
