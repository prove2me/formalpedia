-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_8
-- name    : LeakageRefresh.Continual.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:29.307607+00:00
-- url     : https://prove2.me/theorems/5f1c9839-65b3-47ee-b6f6-c9b6012eecf8
-- title:
--   Lemma 4.8 — the truncated answer table has $\|\mathrm{prob}_z^{>\beta}\|_*\le2$ for $q^{-1/3}\le\beta\le1$
-- statement:
--   Let $n\ge2$ and $q=2^n-1$. Fix the leakage functions of a round (a formal incoming history and the adversary's tape), an answer $z$, and an orthonormal expansion of the table $\mathrm{prob}_z$ on $U_L^2\times U_R^2$. For every $\beta$ with $q^{-1/3}\le\beta\le1$, the truncation $\mathrm{prob}_z^{>\beta}=\sum_{\sigma_j>\beta}\sigma_ju_jv_j^T$ of Eq. (4.7) satisfies
--   $$\big\|\mathrm{prob}_z^{>\beta}\big\|_*\le2 .$$
--   This is the nuclear-norm half of Lemma 4.6.
--
--   Differences from the source:
--   - encoding: a fixed formal incoming history and adversary tape (which fix the two leakage functions) → an arbitrary pair of leakage functions `lp : LeakPair n lam`; reason: every pair of leakage functions arises from some strategy, history and tape, and conversely
--   - reading: the truncation $\mathrm{prob}_z^{>\beta}$ of "an orthonormal expansion" of $\mathrm{prob}_z$ (Eq. (4.7)) → the statement holds for every orthonormal expansion `E : OrthoExpansion (probTable lp z)`; reason: the paper takes an arbitrary expansion and notes the truncation does not depend on it; quantifying over all expansions is that reading
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 34, Lemma 4.8

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.8 (Nuclear norm of the truncated answer table).** For fixed leakage functions
`lp` (a fixed formal incoming history and adversary tape), every answer `z`, every
`q^{−1/3} ≤ β ≤ 1` (`q = 2ⁿ − 1`) and every orthonormal expansion of `prob_z`, the truncation
`prob_z^{>β}` of Eq. (4.7) satisfies `‖prob_z^{>β}‖_* ≤ 2`. -/
theorem lemma_4_8 (n lam : ℕ) (hn : 2 ≤ n) (lp : LeakPair n lam) (z : Answer lam) (β : ℝ)
    (hβ₁ : ((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ)) ≤ β) (hβ₂ : β ≤ 1)
    (E : OrthoExpansion (probTable lp z)) :
    nuclearNorm (E.trunc β) ≤ 2 := by sorry

end LeakageRefresh.Continual
