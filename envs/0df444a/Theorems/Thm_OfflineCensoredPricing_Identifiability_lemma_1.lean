-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_1
-- name    : OfflineCensoredPricing.Identifiability.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:13.478819+00:00
-- url     : https://prove2.me/theorems/ac72eea7-23d3-4d7a-8939-6603e5303dfe
-- title:
--   Lemma 1, p. 18 — |b̂ − b| ≤ α with probability at least 1 − 2K exp(−(1/(9K)) Σᵢ(pᵢ − p̄_avg)² g̲² N α²)
-- statement:
--   Fix an instance satisfying the standing assumptions, with $K$ historical prices $p_i$, the constant $\underline g$ of Assumption 1, and data size $N = \min_i N_i$. Let $\hat b$ be the price-sensitivity estimate of D2ACD (Step 1) computed from the censored sales. For any $\alpha > 0$, $|\hat b - b| \le \alpha$ with probability at least
--   $$1 - 2K\exp\Big(-\frac1{9K}\sum_{i=1}^K\Big(p_i - \frac1K\sum_{j=1}^K p_j\Big)^2\underline g^2 N\alpha^2\Big).$$
--
--   The estimate $\hat b$ is consistent whether or not the problem is identifiable, because it uses only the uncensored part of the sales; the rate improves with the dispersion of the historical prices.
--
--   **Formalization Note** The statement is made on the paper's data assumption $\hat\gamma_i > 0$ for every $i$ (p. 10), which the proof uses ((D.3)–(D.6), p. 43): the outer probability of $\{|\hat b - b| > \alpha\} \cap \{\hat\gamma_i > 0\ \forall i\}$ is at most $2K\exp(\cdots)$. Without it the bound can fail, since $\{\hat\gamma_i = 0\}$ has probability $(1-\gamma_i)^{N_i} > 0$.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 18, Lemma 1 (proof Appendix D.1, pp. 41–45)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Lemma 1** (Convergence of price sensitivity, p. 18). For any `α > 0`, `|b̂ − b| ≤ α` with
probability at least `1 − 2K exp(−(1/(9K)) ∑ᵢ (pᵢ − (1/K)∑ⱼ pⱼ)² g̲² N α²)`, where `N = minᵢ Nᵢ`.
Stated on the data assumption `γ̂ᵢ > 0` for all `i` (p. 10): the outer probability that `|b̂ − b| > α`
and every `γ̂ᵢ > 0` is at most `2K exp(…)`. -/
theorem lemma_1 {K : ℕ} (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ} (hα : 0 < α) :
    dataLaw I Nv {ω | α < |bHat I.toPublic (sales I ω) - I.b| ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤
      ENNReal.ofReal (2 * K * Real.exp (-(1 / (9 * (K : ℝ)) *
        (∑ i, (I.p i - (1 / (K : ℝ)) * ∑ j, I.p j) ^ 2) * I.g ^ 2 * (Nmin Nv : ℝ) * α ^ 2))) := by sorry

end OfflineCensoredPricing.Identifiability
