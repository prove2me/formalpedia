-- Prove2me | Theorems.Thm_MarketMakerAds_Supplement_proposition_2
-- name    : MarketMakerAds.Supplement.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:33:37.7987+00:00
-- url     : https://prove2.me/theorems/e565b4f8-a8a3-4a8f-9145-920cf85a9b90
-- title:
--   Proposition 2 — the Market-Maker price $p^*_M$ increases with risk aversion and, for mean-variance, with $\sigma_A^2$
-- statement:
--   Let the auction clearing price $p$ have law $h$ on $\mathbb R$, with mean $\mu_A$ and variance $\sigma_A^2$, and let $p^*_M$ be the Market-Maker price of eq. (3):
--   $$
--   p^*_M=\mu_A+\beta\,\sigma_A^2\ \text{(mean-variance)},\qquad p^*_M=\frac1\alpha\log\mathbf E_h\big[e^{\alpha p}\big]\ \text{(CARA)}.
--   $$
--
--   1. **Mean-variance, in $\beta$.** If $h$ has a finite second moment, $\beta\mapsto p^*_M$ is nondecreasing on $\beta\ge0$, and strictly increasing when $\sigma_A^2>0$.
--   2. **CARA, in $\alpha$.** If $\mathbf E_h[e^{\alpha p}]<\infty$ for every $\alpha>0$, $\alpha\mapsto p^*_M$ is nondecreasing on $\alpha>0$, and strictly increasing when $h$ is not a point mass.
--   3. **Mean-variance, in $\sigma_A^2$.** Let $\beta\ge0$ and let $h_1,h_2$ have finite second moments and the same mean. If $\sigma_A^2(h_1)\le\sigma_A^2(h_2)$ then $p^*_M(h_1)\le p^*_M(h_2)$, strictly if $\beta>0$ and $\sigma_A^2(h_1)<\sigma_A^2(h_2)$.
--
--   The more risk-averse the buyers, or the more variable the auction clearing price, the higher the premium the Market-Maker contract can charge. Theorem 4 uses item 2 (resp. 1) to rank the populations: the most risk-averse population has the highest $p^*_M$.
--
--   **Formalization Note** "Increasing" is stated both weakly and strictly, under the non-degeneracy that makes it strict. $\alpha=0$ is excluded since (3) divides by $\alpha$.
--
--   Differences from the source:
--   - encoding: α ≥ 0 → α > 0; reason: eq. (3) divides by α, so α = 0 is an undefined case (Lean's 1/0 = 0)
--   - reading: "increasing" → nondecreasing in general and strictly increasing when σ²_A > 0 (mean-variance), resp. when h is not a point mass (CARA); reason: the word is ambiguous and the proof (p.38) shows (p*_M)′ ≥ 0; both readings are stated, neither is dropped
--   - reading: "increasing function of the variance σ²_A" → comparison of two clearing-price laws with the same mean; reason: (3) is read as a function of (µ_A, σ²_A) with µ_A held fixed
--   - generalization: clearing price with a density on [0, ∞) → any probability law on ℝ with a finite second moment (mean-variance), resp. finite E[e^{αp}] for α > 0 (CARA); reason: these are the moments that make (3) a real number; every law of the paper has them
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Proposition 2, p.19; proof Appendix E, p.38

import Mathlib
import Definitions.Def_MarketMakerAds_pStar

open MeasureTheory

namespace MarketMakerAds

namespace Supplement

/-- **Proposition 2 (Market-Maker Price as a Function of Risk), p.19 (proof Appendix E, p.38).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Proposition 2, p.19:
"The revenue-optimal Market-Maker price p*_M is an increasing function of the risk aversion
parameter (α in the CARA model and β in the Mean-variance model). Further, in the Mean-variance
model, p*_M is an increasing function of the variance of the auction clearing price (σ²_A)."

`p*_M` is the published closed form (3), `pStar`: `µ_A + β σ²_A` (mean-variance) and
`(1/α) log E[e^{α p}]` (CARA), for the law `h` of the clearing price. Then
1. (mean-variance, in `β`) if `h` has a finite second moment, `β ↦ p*_M` is nondecreasing on
   `β ≥ 0`, and strictly increasing there when `σ²_A > 0`;
2. (CARA, in `α`) if `E[e^{α p}] < ∞` for every `α > 0`, `α ↦ p*_M` is nondecreasing on `α > 0`,
   and strictly increasing there when `h` is not a point mass;
3. (mean-variance, in `σ²_A`) for `β ≥ 0` and two laws with finite second moments and equal means,
   `σ²_A(h₁) ≤ σ²_A(h₂)` gives `p*_M(h₁) ≤ p*_M(h₂)`, strictly when `β > 0` and
   `σ²_A(h₁) < σ²_A(h₂)`.

**Formalization Note** "Increasing" is stated both weakly (what the proof on p.38 shows,
`(p*_M)′(α) ≥ 0`) and strictly under the non-degeneracy that makes it strict, so both readings are
covered. `α = 0` is excluded: (3) divides by `α` (Lean's `1/0 = 0`). "Increasing in σ²_A" compares
laws with the same mean `µ_A`, as (3) is read as a function of `(µ_A, σ²_A)`. -/
theorem proposition_2 :
    -- 1. mean-variance: increasing in β
    (∀ (h : Measure ℝ) [IsProbabilityMeasure h], Integrable (fun p => p ^ 2) h →
      MonotoneOn (fun β : ℝ => pStar (.meanVariance β) h) (Set.Ici 0) ∧
      (0 < ∫ p, (p - ∫ q, q ∂h) ^ 2 ∂h →
        StrictMonoOn (fun β : ℝ => pStar (.meanVariance β) h) (Set.Ici 0))) ∧
    -- 2. CARA: increasing in α
    (∀ (h : Measure ℝ) [IsProbabilityMeasure h],
      (∀ α : ℝ, 0 < α → Integrable (fun p => Real.exp (α * p)) h) →
      MonotoneOn (fun α : ℝ => pStar (.cara α) h) (Set.Ioi 0) ∧
      ((∀ x : ℝ, h ≠ Measure.dirac x) →
        StrictMonoOn (fun α : ℝ => pStar (.cara α) h) (Set.Ioi 0))) ∧
    -- 3. mean-variance: increasing in the variance σ²_A
    (∀ β : ℝ, 0 ≤ β → ∀ (h₁ h₂ : Measure ℝ) [IsProbabilityMeasure h₁] [IsProbabilityMeasure h₂],
      Integrable (fun p => p ^ 2) h₁ → Integrable (fun p => p ^ 2) h₂ →
      ∫ p, p ∂h₁ = ∫ p, p ∂h₂ →
      ((∫ p, (p - ∫ q, q ∂h₁) ^ 2 ∂h₁ ≤ ∫ p, (p - ∫ q, q ∂h₂) ^ 2 ∂h₂ →
          pStar (.meanVariance β) h₁ ≤ pStar (.meanVariance β) h₂) ∧
        (0 < β → ∫ p, (p - ∫ q, q ∂h₁) ^ 2 ∂h₁ < ∫ p, (p - ∫ q, q ∂h₂) ^ 2 ∂h₂ →
          pStar (.meanVariance β) h₁ < pStar (.meanVariance β) h₂))) := by sorry

end Supplement

end MarketMakerAds
