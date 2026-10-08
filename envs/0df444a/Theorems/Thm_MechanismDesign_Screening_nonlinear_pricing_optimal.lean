-- Prove2me | Theorems.Thm_MechanismDesign_Screening_nonlinear_pricing_optimal
-- name    : MechanismDesign.Screening.nonlinear_pricing_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:04:53.891482+00:00
-- url     : https://prove2.me/theorems/a85da17f-da4a-4783-a7e1-eb043c857fe3
-- title:
--   Proposition 2.6 -- the optimal nonlinear price schedule under regularity
-- statement:
--   Consider the nonlinear pricing model of §2.3: cost $cq$ with $c>0$, buyer utility $\theta\nu(q)-t$ with $\nu(0)=0$, $\nu$ twice differentiable, $\nu'>0$ and $\nu''<0$ on $[0,\infty)$, $\bar\theta\nu'(0)>c$ and $\lim_{q\to\infty}\bar\theta\nu'(q)<c$; types on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, with distribution $F$ and positive density $f$. Suppose $F$ is regular (Assumption 2.1). Let $q:[\underline\theta,\bar\theta]\to\mathbb R_+$ satisfy, for every $\theta$:
--
--   1. if $\nu'(0)\Big(\theta-\dfrac{1-F(\theta)}{f(\theta)}\Big)\le c$, then $q(\theta)=0$;
--   2. otherwise,
--   $$\nu'(q(\theta))\Big(\theta-\frac{1-F(\theta)}{f(\theta)}\Big)=c ;$$
--
--   and let
--   $$t(\theta)=\theta\,\nu(q(\theta))-\int_{\underline\theta}^{\theta}\nu(q(x))\,dx .$$
--   Then $(q,t)$ is incentive-compatible and individually rational, and it maximizes the seller's expected profit $\int_{\underline\theta}^{\bar\theta}\big(t(\theta)-cq(\theta)\big)f(\theta)\,d\theta$ among all incentive-compatible, individually rational direct mechanisms of §2.3.
--
--   The result exhibits the classic features of monopolistic screening: no distortion at the top ($\nu'(q(\bar\theta))\bar\theta=c$) and downward quantity distortion for lower types.
--
--   **Formalization Note** The book asserts "an expected profit maximizing choice", not uniqueness; the statement asserts optimality of the displayed $(q,t)$ among incentive-compatible, individually rational deterministic mechanisms (the book's Definition 2.5), and that it is itself incentive-compatible and individually rational. In case 2 the equation is a hypothesis on $q(\theta)$; under the standing assumptions it has a unique solution, which is positive. No integrability hypotheses are placed on competitors: incentive compatibility makes $q$ monotone and bounded, and then $t$ bounded and measurable.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.24, Proposition 2.6 (model pp.18–19, Assumption 2.1 p.23)

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model
import Definitions.Def_MechanismDesign_Screening_NonlinearPricing

namespace MechanismDesign.Screening

/-- **Proposition 2.6**, p.24. Suppose `F` is regular (Assumption 2.1). A quantity schedule `q`
with (i) `q(θ) = 0` whenever `ν′(0)(θ − (1 − F(θ))/f(θ)) ≤ c`, and (ii) otherwise
`ν′(q(θ))(θ − (1 − F(θ))/f(θ)) = c`, together with the payment
`t(θ) = θ ν(q(θ)) − ∫_{θ̲}^{θ} ν(q(x)) dx`, is an incentive-compatible, individually rational
direct mechanism that maximizes the seller's expected profit among all incentive-compatible,
individually rational direct mechanisms of §2.3. -/
theorem nonlinear_pricing_optimal {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (E : NonlinearEnv θhi) (hreg : IsRegular D) (m : QuantityMechanism θlo θhi)
    (hq : ∀ θ ∈ Set.Icc θlo θhi,
      (deriv E.ν 0 * virtualValuation D θ ≤ E.c → m.q θ = 0) ∧
      (E.c < deriv E.ν 0 * virtualValuation D θ →
        deriv E.ν (m.q θ) * virtualValuation D θ = E.c))
    (ht : ∀ θ ∈ Set.Icc θlo θhi, m.t θ = θ * E.ν (m.q θ) - ∫ x in θlo..θ, E.ν (m.q x)) :
    m.IsIC E ∧ m.IsIR E ∧
      ∀ m' : QuantityMechanism θlo θhi, m'.IsIC E → m'.IsIR E →
        expectedProfit D E m' ≤ expectedProfit D E m := by sorry

end MechanismDesign.Screening
