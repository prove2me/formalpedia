-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_theorem_B1
-- name    : LimitedPriceChanges.AlgorithmI.theorem_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:39.289715+00:00
-- url     : https://prove2.me/theorems/12a96d5c-673b-4ed3-b6ec-0649c8b0a1f7
-- title:
--   Theorem B1, p. 21 — if ℙ{‖ẑ−z‖ ≥ ϵ} ≤ K₁₄e^{−nK₁₅ϵ²} + K₁₆/n then G*(z) − 𝔼[G(p̂*, ŷ*, z)] ≤ K₁₇/n
-- statement:
--   Let $\mathcal P=[p^l,p^h]$, let $\mathcal Y$ be a nonempty finite set of nonnegative integers, and let $\mathcal Z\subset\mathbb R^k$ be compact and convex. Let $G(p,y,\mathbf z)$ be an objective with a price selection $p^*_y(\mathbf z)$ on $\mathcal Z$, let $\mathbf z\in\mathcal Z$ be the true parameter, and suppose Assumption A holds at $\mathbf z$. Let $\hat y(\cdot)$ be a level selection, so that $\hat y(\mathbf z')\in\mathcal Y^*(\mathbf z')$ for every $\mathbf z'\in\mathcal Z$.
--
--   On a probability space, let $\hat{\mathbf z}_n$ ($n\ge1$) be $\mathcal Z$-valued estimators of $\mathbf z$ such that, for constants $K_{14},K_{15},K_{16}>0$, every $n\ge1$ and every $\epsilon>0$,
--   $$
--   \mathbb P\{\|\hat{\mathbf z}_n-\mathbf z\|\ge\epsilon\}\le K_{14}e^{-nK_{15}\epsilon^2}+\frac{K_{16}}{n}. \tag{10}
--   $$
--   Set $\hat y^*=\hat y(\hat{\mathbf z}_n)\in\mathcal Y^*(\hat{\mathbf z}_n)$ and $\hat p^*=p^*_{\hat y^*}(\hat{\mathbf z}_n)\in\mathcal P^*_{\hat y^*}(\hat{\mathbf z}_n)$. Then there is a constant $K_{17}>0$ such that for all large enough $n$,
--   $$
--   G^*(\mathbf z)-\mathbb E\big[G(\hat p^*,\hat y^*,\mathbf z)\big]\le\frac{K_{17}}{n}. \tag{11}
--   $$
--
--   The theorem converts a large-deviation bound on a parameter estimate into a $1/n$ bound on the expected optimality gap of the plug-in decision; it does not require the optimal decision to be unique.
--
--   **Formalization Note** The continuous and discrete decisions are scalar ($r_1=r_2=1$, the paper's own setting in §2). $\hat p^*$ is the value of the price selection of Assumption A(iii) at $(\hat y^*,\hat{\mathbf z}_n)$, the decision the printed proof analyses ((19)–(21)); for an arbitrary other maximizer in $\mathcal P^*_{\hat y^*}(\hat{\mathbf z}_n)$ the proof's Lipschitz step has no support. (10) is assumed for every $n\ge1$. The estimators and the plug-in profit $\omega\mapsto G(\hat p^*,\hat y^*,\mathbf z)$ are assumed measurable, which the expectation presupposes. The expectation of the nonnegative gap $G^*(\mathbf z)-G(\hat p^*,\hat y^*,\mathbf z)$ is a lower Lebesgue integral in $[0,\infty]$, and probabilities are compared in $[0,\infty]$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), pp. 20–21, Appendix B, Theorem B1, (10)–(11)

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_DataBasedOptimization

namespace LimitedPriceChanges.AlgorithmI

open MeasureTheory

/-- **Theorem B1** (p. 21), for a scalar continuous decision `p ∈ 𝒫 = [pl, ph]` and a scalar
discrete decision `y ∈ 𝒴` (a nonempty finite set of naturals), with parameter
`z ∈ 𝒵 ⊂ ℝᵏ`, `𝒵` compact and convex, under Assumption A at `z`. Let `ẑₙ` (`n ≥ 1`) be
`𝒵`-valued estimators of `z` on a probability space with
`ℙ{‖ẑₙ − z‖ ≥ ϵ} ≤ K₁₄ e^{−n K₁₅ ϵ²} + K₁₆ / n` (10) for every `n ≥ 1` and `ϵ > 0`, for some
`K₁₄, K₁₅, K₁₆ > 0`. Let `ŷ* = ysel(ẑₙ) ∈ 𝒴*(ẑₙ)` and `p̂* = p*_{ŷ*}(ẑₙ)`. Then there is
`K₁₇ > 0` such that for all large enough `n`, `G*(z) − 𝔼[G(p̂*, ŷ*, z)] ≤ K₁₇ / n` (11). -/
theorem theorem_B1 {k : ℕ} (pl ph : ℝ) (Y : Finset ℕ) (hY : Y.Nonempty)
    (Z : Set (EuclideanSpace ℝ (Fin k))) (hZc : IsCompact Z) (hZv : Convex ℝ Z)
    (G : ℝ → ℕ → EuclideanSpace ℝ (Fin k) → ℝ) (pstar : ℕ → EuclideanSpace ℝ (Fin k) → ℝ)
    (hsel : IsPriceSelection pl ph Y Z G pstar)
    (z : EuclideanSpace ℝ (Fin k)) (hz : z ∈ Z) (hA : AssumptionA pl ph Y hY Z G pstar z)
    (ysel : EuclideanSpace ℝ (Fin k) → ℕ) (hysel : IsLevelSelection Y Z G pstar ysel)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin k)) (hmeas : ∀ n, Measurable (zhat n))
    (hzZ : ∀ n ω, zhat n ω ∈ Z)
    (hGmeas : ∀ n, Measurable (fun ω => G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z))
    (K₁₄ K₁₅ K₁₆ : ℝ) (hK₁₄ : 0 < K₁₄) (hK₁₅ : 0 < K₁₅) (hK₁₆ : 0 < K₁₆)
    (h10 : ∀ n : ℕ, 1 ≤ n → ∀ ϵ : ℝ, 0 < ϵ →
      P {ω | ϵ ≤ ‖zhat n ω - z‖} ≤
        ENNReal.ofReal (K₁₄ * Real.exp (-((n : ℝ) * K₁₅ * ϵ ^ 2)) + K₁₆ / (n : ℝ))) :
    ∃ K₁₇ : ℝ, 0 < K₁₇ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∫⁻ ω, ENNReal.ofReal (optValue Y hY G pstar z -
          G (pstar (ysel (zhat n ω)) (zhat n ω)) (ysel (zhat n ω)) z) ∂P ≤
        ENNReal.ofReal (K₁₇ / (n : ℝ)) := by sorry

end LimitedPriceChanges.AlgorithmI
