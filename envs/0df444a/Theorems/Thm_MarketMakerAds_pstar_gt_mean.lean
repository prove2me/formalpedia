-- Prove2me | Theorems.Thm_MarketMakerAds_pstar_gt_mean
-- name    : MarketMakerAds.pstar_gt_mean
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:23.773323+00:00
-- url     : https://prove2.me/theorems/03d928ca-3845-4687-8339-f13e2ec0fa72
-- title:
--   The Market-Maker markup is positive, $p^*_M>\mu_A$ (corrected: $\beta>0$)
-- statement:
--   Let the auction clearing price $p$ have law $h$ with mean $\mu_A$.
--
--   1. **Nonnegative markup.** For $\beta\ge0$, resp. $\alpha>0$, if $p$ has a finite second moment (and, for CARA, $\mathbf E[e^{\alpha p}]<\infty$), then $\mu_A\le p^*_M$.
--   2. **Positive markup.** For $\beta>0$, resp. $\alpha>0$, suppose the negative part of $p$ has a finite second moment and $p_{\max}$ is the top of the support of $h$ without an atom:
--      - $p\le p_{\max}$ almost surely,
--      - $h\big((v,\infty)\big)>0$ for every $v<p_{\max}$,
--      - $h(\{p_{\max}\})=0$.
--
--      Then
--
--   $$
--   \mu_A<p^*_M .
--   $$
--
--   The markup $p^*_M-\mu_A$ is what the buyers of the contract pay above the expected clearing price; its positivity is why the seller's revenue increases in Theorem 3.
--
--   Differences from the source:
--   - correction: "for both utility models $p^*_M>\mu_A$" with $\beta\ge0$ → strict inequality only for $\beta>0$; reason: at $\beta=0$, $p^*_M=\mu_A$ for every law (e.g. $c$ uniform on $[0,1]$: $p^*_M=\mu_A=1/2$).
--   - encoding: $\alpha\ge0$ → $\alpha>0$; reason: (3) divides by $\alpha$ and is undefined at $\alpha=0$.
--   - generalization: a clearing-price density on $[0,\infty)$ → for the strict inequality, any law on $\mathbb R$ with top of support $p_{\max}$, no atom at $p_{\max}$ and negative part with a finite second moment; for the non-strict inequality, any law with a finite second moment (and a finite exponential moment for CARA); reason: a density on $[0,p_{\max}]$ satisfies these hypotheses; the moments are what makes $\mu_A$, $\sigma_A^2$ and $\mathbf E[e^{\alpha p}]$ finite.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, p.17 (below Proposition 1, "p*_M ≥ µ_A"); Proof of Theorem 3, p.19 ("for both utility models p*_M > µ_A")

import Mathlib
import Definitions.Def_MarketMakerAds_pStar

open MeasureTheory

namespace MarketMakerAds

/-- **The Market-Maker markup is positive: `p*_M > µ_A` (corrected: `β > 0`), pp.17 and 19.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, p.17: "one can see
that the price markup is non-negative (i.e., p*_M ≥ µ_A, where µ_A = E_p[p]), because of the
concavity of the log(·) function", and Proof of Theorem 3, p.19: "Since for both utility models
p*_M > µ_A, the seller's expected revenue strictly increases."

1. (non-strict) For `β ≥ 0`, resp. `α > 0`, and every law of the clearing price with the needed
   moments, `µ_A ≤ p*_M`.
2. (strict) For `β > 0`, resp. `α > 0`, and a law with `p ≤ p_max` almost surely, mass in every
   interval `(v, ∞)` with `v < p_max`, and no atom at `p_max`: `µ_A < p*_M`.

**Formalization Note** With `β = 0`, `p*_M = µ_A` and the strict inequality fails, so it assumes
`β > 0`. `α > 0` is needed for (3) to be defined. `p_max` is the top of the support, given by the
two hypotheses `p ≤ p_max` a.s. and `P(p > v) > 0` for `v < p_max`; no density is assumed, only
no atom at `p_max`. -/
theorem pstar_gt_mean (h : Measure ℝ) [IsProbabilityMeasure h] :
    (∀ m : RiskModel, m.IsAdmissible →
      Integrable (fun p => p ^ 2) h →
      (∀ α : ℝ, m = .cara α → Integrable (fun p => Real.exp (α * p)) h) →
      ∫ p, p ∂h ≤ pStar m h) ∧
    (∀ m : RiskModel, m.IsPositive →
      Integrable (fun p => (max (-p) 0) ^ 2) h →
      ∀ pmax : ℝ, (∀ᵐ p ∂h, p ≤ pmax) → (∀ v < pmax, 0 < h (Set.Ioi v)) → h {pmax} = 0 →
      ∫ p, p ∂h < pStar m h) := by sorry

end MarketMakerAds
