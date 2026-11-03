-- Prove2me | Theorems.Thm_MultiPurchaseMNL_approximation_ratio
-- name    : MultiPurchaseMNL.approximation_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:51.493394+00:00
-- url     : https://prove2.me/theorems/4a9bf29b-922e-4530-a3f7-8dbc85d00340
-- title:
--   §4.3, p.19 — approximation ratio: $\mathcal R(\tilde S)\ge(1-2\epsilon)\,\mathcal R(S^*)$
-- statement:
--   Let $\varepsilon\in(0,1)$ and let $\varepsilon'=1/\lceil2/\varepsilon\rceil$ be the internal accuracy of the program `ptas`, so that $1/\varepsilon'$ is an integer and $\varepsilon'\le\varepsilon/2$. Under standard Gumbel shocks and the standing assumptions, the assortment $\tilde S$ returned by `ptas` satisfies, for every assortment $S$ (in particular an optimal $S^*$),
--   $$
--   \mathcal R(\tilde S)\ \ge\ (1-2\varepsilon')\,\mathcal R(S).
--   $$
--   This is the chain $\mathcal R(\tilde S)\ge\sum_{\tilde S}r_i\tilde\pi_i\ge\sum_{S^*}r_i\tilde\pi_i\ge(1-2\epsilon)\sum_{S^*}r_i\pi(i,S^*)=(1-2\epsilon)\mathcal R(S^*)$ of §4.3 for the algorithm as a whole.
--
--   Differences from the source:
--
--   - reading: S̃ the knapsack output for the right guesses, ϵ with 1/ϵ ∈ ℕ → S̃ = output of ptas, the candidate of largest exact revenue over all guesses, run at ε' = 1/⌈2/ε⌉₊ for ε ∈ (0,1); reason: the right guess is unknown to the algorithm, which must select among candidates (reading 5); ε' realizes §4.1's integrality assumption (reading 3)
--   - encoding: R(S̃) ≥ (1 − 2ϵ)·R(S*) for an optimal S* → (1 − 2ε')·R(S) ≤ R(S̃) for every S; reason: equivalent, since R(S*) ≥ R(S) and 1 − 2ε' ≥ 0
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §4.3, p.19, "Approximation ratio"

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_Algorithm

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §4.3, p.19, "Approximation ratio":
`R(S̃) = Σ_{i∈S̃} rᵢ·π(i,S̃) ≥ Σ_{i∈S̃} rᵢπ̃ᵢ ≥ Σ_{i∈S∗} rᵢπ̃ᵢ ≥ (1 − 2ϵ)·Σ_{i∈S∗} rᵢ·π(i,S∗)
= (1 − 2ϵ)·R(S∗)`.

For the program `ptas` run at `ε ∈ (0, 1)`, whose internal accuracy is `ε' = 1/⌈2/ε⌉₊` (`epsInt`),
the returned assortment `S̃` satisfies `R(S̃) ≥ (1 − 2ε')·R(S)` for every assortment `S`.

**Formalization Note.** The paper's `ϵ` with `1/ϵ` integer is the program's `ε'`. Comparing with
every `S` is comparing with an optimal `S*`. -/
theorem approximation_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hI : I.Standing) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (S : Finset (Fin n)) :
    (1 - 2 * epsInt ε) * R μ I S ≤ R μ I (output I ε) := by sorry

end MultiPurchaseMNL
