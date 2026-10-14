-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_theorem_3
-- name    : InfoRelaxTS.Gap.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:16.576872+00:00
-- url     : https://prove2.me/theorems/690f4244-edd4-4ac6-8f52-46f605b7c4df
-- title:
--   Theorem 3, pp. 26–27 — suboptimality gaps of TS, IRS.FH and IRS.V-Zero for L-smooth natural exponential families
-- statement:
--   Consider a $K$-armed Bayesian bandit whose rewards form a natural exponential family as in §2.2: arm $a$ has reference measure $h_a$ and log-partition function $A_a$, normalized so that $\int e^{\theta r}h_a(dr)=e^{A_a(\theta)}$ for all $\theta\in\mathbb R$, and hyperparameter $y_a=(\xi_a,\nu_a)$. Suppose all log-partition functions are $L$-smooth,
--   $$\frac{d^2}{d\theta^2}A_a(\theta)\le L\qquad(\theta\in\mathbb R,\ a\in\mathcal A),$$
--   and $\nu_a=\nu>0$ for all $a$, each prior being proper and the rewards integrable (3). Let $\pi^{\rm TS}$, $\pi^{\rm IRS.FH}$ and $\pi^{\rm IRS.V\text{-}Zero}$ be Thompson sampling, IRS.FH and IRS.V-Zero with any measurable tie-breaking rules. Then for every $T\ge2$:
--
--   1. $$W^{\rm TS}(T,y)-V(\pi^{\rm TS},T,y)\le2\sqrt L\left[\frac1{\sqrt\nu}+\sqrt{2\log T}\times\left(\frac K{\sqrt\nu}+2\sqrt{KT}\right)\right];$$
--   2. $$W^{\rm IRS.FH}(T,y)-V(\pi^{\rm IRS.FH},T,y)\le2\sqrt L\left[\frac1{\sqrt\nu}+\sqrt{2\log T}\times\left(\frac K{\sqrt\nu}+2\sqrt{KT}-\frac13\sqrt{\frac TK}\right)\right];$$
--   3. $$W^{\rm IRS.V\text{-}Zero}(T,y)-V(\pi^{\rm IRS.V\text{-}Zero},T,y)\le\sqrt L\left[\frac1{\sqrt\nu}+\sqrt{2\log T}\times\left(\frac K{\sqrt\nu}+2\sqrt{KT}-\frac13\sqrt{\frac TK}\right)\right].$$
--
--   Each left side is the suboptimality gap of a policy against its own performance bound. All three are of order $\sqrt{KT\log T}$, and the IRS policies improve the leading coefficient or the additive term relative to Thompson sampling.
--
--   **Formalization Note** $\Theta_a=\mathbb R$. $L$-smoothness also requires $A_a$ to be $C^2$, so that the bound on `deriv (deriv A)` is not satisfied by a junk value; this follows from normalization. $K\ge1$ is assumed. Properness of the prior and (3) are required only at the prior belief $y$. $W^{\rm IRS.FH}$ is defined by its closed form (33). The policies see only the current belief and their own samples: their action laws are functions of the remaining horizon and the current belief, and $V$ follows the outer loop of Algorithms 1 and 3. The argmax selector and the optimal-allocation selector are arbitrary measurable tie-breaking rules, and the bounds are claimed for all of them. Parts 2 and 3 are stated as printed.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 26–27, Theorem 3, (59)–(62)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

open MeasureTheory ProbabilityTheory

namespace InfoRelaxTS.Gap

theorem theorem_3 {K : ℕ} [NeZero K] (M : NEFModel K) (L ν : ℝ) (ξ : Fin K → ℝ) (T : ℕ)
    (sel : (Fin K → ℝ) → Fin K) (asel : ℕ → (Fin K → ℕ → ℝ) → (Fin K → ℕ))
    (hnorm : IsNormalized M) (hsmooth : IsLSmooth M L)
    (hprior : ∀ a, IsProperPrior M a (ξ a, ν))
    (hint : ∀ a, Integrable (fun r : ℝ => r) (predLaw M a (ξ a, ν)))
    (hsel : IsArgmaxSel sel) (hsel_meas : Measurable sel)
    (hasel : IsOptAllocSel asel) (hasel_meas : ∀ T', Measurable (asel T'))
    (hT : 2 ≤ T) :
    WTS M T (fun a => (ξ a, ν)) - V M (tsPol M sel) T (fun a => (ξ a, ν)) ≤
        2 * Real.sqrt L * (1 / Real.sqrt ν + Real.sqrt (2 * Real.log T) *
          ((K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T))) ∧
      WFH M T (fun a => (ξ a, ν)) - V M (fhPol M sel) T (fun a => (ξ a, ν)) ≤
        2 * Real.sqrt L * (1 / Real.sqrt ν + Real.sqrt (2 * Real.log T) *
          ((K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T)
            - (1 / 3) * Real.sqrt ((T : ℝ) / K))) ∧
      WVZ M T (fun a => (ξ a, ν)) - V M (vzPol M asel sel) T (fun a => (ξ a, ν)) ≤
        Real.sqrt L * (1 / Real.sqrt ν + Real.sqrt (2 * Real.log T) *
          ((K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T)
            - (1 / 3) * Real.sqrt ((T : ℝ) / K))) := by sorry

end InfoRelaxTS.Gap
