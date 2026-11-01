-- Prove2me | Theorems.Thm_OnlineWass_proposition_1_bound
-- name    : OnlineWass.proposition_1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:52.119317+00:00
-- url     : https://prove2.me/theorems/03fb3aa0-e71c-45cc-9338-de6daa2d35b1
-- title:
--   Proposition 1 — shared minimizer and $\mathbb E[R^*_T]\le\sum_t\min L_t$, with $\mathbb E[R^*_T]\le L(p)$ (corrected: complementary tie-break in (6))
-- statement:
--   Under the model's hypotheses, for $c\ge0$ and independent $\theta_t\sim\mathcal P_t$, write $L_t(p):=\gamma_t^\top p+\mathcal P_t h(p;\theta)$ with $\gamma_t:=\mathcal P_t g(x^*(\theta);\theta)$.
--
--   1. For every $p\ge0$ and every profile $\mathcal H$, $R^*_T(\mathcal H)\le p^\top c+\sum_{t=1}^T h(p;\theta_t)$, and so $\mathbb E[R^*_T]\le L(p)$.
--   2. If $p^*\ge0$ and $x^*(\theta)$ is a measurable maximizer of $f(x;\theta)-(p^*)^\top g(x;\theta)$ over $\mathcal X$, then $p^*\in\operatorname{argmin}_{p\ge0}L_t(p)$ for each $t$.
--   3. If $(p^*,x^*)$ is a fluid plan for $\mathcal P$, then for all $p_1,\dots,p_T\ge0$
--
--   $$
--   \mathbb E[R^*_T]\le\sum_{t=1}^T L_t(p_t),
--   $$
--
--   that is $\mathbb E[R^*_T]\le\sum_t\min_{p_t\ge0}L_t(p_t)$, which by clause 2 equals $\min_{p\ge0}\sum_t L_t(p)$.
--
--   Clause 1 is the weak-duality step that starts the proof of Theorem 3.
--
--   Differences from the source:
--   - correction: second clause, E[R*_T] ≤ min_{p≥0} Σₜ Lₜ(p) = Σₜ min_{pₜ≥0} Lₜ(pₜ), with γₜ from any maximizer x* in (6) → the same bound, as E[R*_T] ≤ Σₜ Lₜ(pₜ) for all pₜ ≥ 0, with (p*, x*) a fluid plan for 𝒫 (IsFluidPlan: Σₜγₜ ≤ c and complementary slackness); reason: with a free tie-break the clause fails: on the instance of the (10) correction with x*(a)=0, Σₜ Lₜ(p*) = T/2 < 5T/8 = E[R*_T]
--   - generalization: first clause for p* a dual optimum (5) and x* the argmax of (6) → for any p* ≥ 0 and any measurable maximizer x*; reason: the proof uses only that x*(θ) maximizes the Lagrangian; a plan's p* is a dual optimum (lemma_5)
--   - generalization: Proposition 1's two clauses → an added clause: pathwise R*_T(H) ≤ pᵀc + Σₜ h(p;θₜ) and E[R*_T] ≤ L(p) for every p ≥ 0; reason: the form used in the proof of Theorem 3, p.56; an extra conclusion
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - encoding: min_{p≥0} Σₜ Lₜ(p) = Σₜ min_{pₜ≥0} Lₜ(pₜ) → E[R*_T] bounded by Σₜ Lₜ(pₜ) for every choice pₜ ≥ 0, with clause 2 giving the common minimizer; reason: a bound at every point is a bound at the minimum; the minima are attained at p* by clause 2
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Proposition 1, p.15, and the form used in the proof of Theorem 3, p.56

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_dual
import Definitions.Def_OnlineWass_IsFluidPlan
import Definitions.Def_OnlineWass_benchmarks

open MeasureTheory

namespace OnlineWass

/-- **Proposition 1, Jiang, Li & Zhang, arXiv:2012.06961v3, p.15, corrected, with the form the proof of
Theorem 3 uses (p.56).** With `Lₜ(p) := γₜᵀp + 𝒫ₜh(p; θ)` (p.15):
(1) for every `p ≥ 0`, pathwise `R*_T(H) ≤ pᵀc + Σₜ h(p; θₜ)`, and so `𝔼[R*_T] ≤ L(p)`;
(2) the first clause of Proposition 1: if `x*(θ)` is a measurable maximizer of
`f(x; θ) − (p*)ᵀg(x; θ)` over `𝒳` and `γₜ := 𝒫ₜ g(x*(θ); θ)`, then `p* ∈ argmin_{p≥0} Lₜ(p)` for each `t`;
(3) the second clause: if `(p*, x*)` is a plan for `𝒫` (`IsFluidPlan`, complementary tie-break in (6)), then
`𝔼[R*_T] ≤ Σₜ Lₜ(pₜ)` for all `p₁, …, p_T ≥ 0`, that is `𝔼[R*_T] ≤ Σₜ min_{pₜ≥0} Lₜ(pₜ)`, which by (2)
equals `min_{p≥0} Σₜ Lₜ(p)`.

**Formalization Note.** With a free tie-break in (6) the second clause is false (the instance of the
`IsFluidPlan` correction); a plan's `p*` is a dual optimum (5) by `OnlineWass.lemma_5`. `R*_T` is
integrable by `OnlineWass.regret_wellDefined`. -/
theorem proposition_1_bound {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M) (hT : 0 < T)
    (c : Fin m → ℝ) (hc : 0 ≤ c)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)]
    (p : Fin m → ℝ) (hp : 0 ≤ p) :
    (∀ H : Fin T → Θ, offlineValue M c H ≤ ∑ i, p i * c i + ∑ t, h M p (H t)) ∧
      ∫ H, offlineValue M c H ∂Measure.pi P ≤ dual M c P p ∧
      (∀ (pstar : Fin m → ℝ) (xstar : Θ → Fin k → ℝ), 0 ≤ pstar → Measurable xstar →
        (∀ θ, xstar θ ∈ M.X) →
        (∀ θ, IsMaxOn (fun x => M.lagrangian pstar x θ) M.X (xstar θ)) →
        ∀ (t : Fin T) (p' : Fin m → ℝ), 0 ≤ p' →
          ∑ i, gammaHat M P xstar t i * pstar i + LQ M (P t) pstar ≤
            ∑ i, gammaHat M P xstar t i * p' i + LQ M (P t) p') ∧
      (∀ (pstar : Fin m → ℝ) (xstar : Θ → Fin k → ℝ), IsFluidPlan M c P pstar xstar →
        ∀ ps : Fin T → Fin m → ℝ, (∀ t, 0 ≤ ps t) →
          ∫ H, offlineValue M c H ∂Measure.pi P ≤
            ∑ t, (∑ i, gammaHat M P xstar t i * ps t i + LQ M (P t) (ps t))) := by sorry

end OnlineWass
