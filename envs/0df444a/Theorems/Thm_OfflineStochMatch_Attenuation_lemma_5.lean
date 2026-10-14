-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_lemma_5
-- name    : OfflineStochMatch.Attenuation.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:57.616167+00:00
-- url     : https://prove2.me/theorems/f38eb498-6f70-4245-a259-6975397c71f0
-- title:
--   Lemma 5, p. 12 — Chernoff: Pr[Σ B_i < (1+ε)µ] ≥ 1 − exp(−ε²µ/(2+ε))
-- statement:
--   Fix $\varepsilon > 0$. Let $B_1, \dots, B_k$ be independent Bernoulli random variables with $\Pr[B_i = 1] = q_i \in [0,1]$, and let $\mu = \sum_{i=1}^k q_i$. Then
--   $$\Pr\Bigl[\sum_{i=1}^k B_i < (1+\varepsilon)\mu\Bigr] \;\ge\; 1 - \exp\Bigl(-\frac{\varepsilon^2}{2+\varepsilon}\,\mu\Bigr).$$
--
--   This is the standard multiplicative Chernoff bound for the upper tail. In the analysis of Theorem 1 it gives bound (10) for vertices of large patience.
--
--   **Formalization Note** The probability is the finite sum, over the $2^k$ outcomes, of the product of the Bernoulli weights.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 12, Lemma 5

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem lemma_5 (k : ℕ) (q : Fin k → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    1 - Real.exp (-(ε ^ 2 / (2 + ε) * ∑ j, q j))
      ≤ ∑ b : Fin k → Bool,
          coinWeight q b *
            (if (((Finset.univ.filter (fun i => b i = true)).card : ℕ) : ℝ) < (1 + ε) * ∑ j, q j
              then 1 else 0) := by sorry

end OfflineStochMatch.Attenuation
