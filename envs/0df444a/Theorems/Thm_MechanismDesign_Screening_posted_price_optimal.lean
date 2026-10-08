-- Prove2me | Theorems.Thm_MechanismDesign_Screening_posted_price_optimal
-- name    : MechanismDesign.Screening.posted_price_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:43.415213+00:00
-- url     : https://prove2.me/theorems/7d6becb7-adc4-4100-a84e-ad0b26ccfcbc
-- title:
--   Proposition 2.5 -- a posted price at $p^*\in\arg\max p(1-F(p))$ maximizes expected revenue
-- statement:
--   A seller sells one indivisible good to one buyer whose valuation $\theta$ has cumulative distribution function $F$ with density $f>0$ on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$. Suppose
--   $$p^*\in\operatorname*{arg\,max}_{p\in[\underline\theta,\bar\theta]}\; p\,\big(1-F(p)\big).$$
--   Consider the direct mechanism
--   $$q(\theta)=\begin{cases}1 & \text{if } \theta>p^*,\\ 0 & \text{if } \theta<p^*,\end{cases}\qquad t(\theta)=\begin{cases}p^* & \text{if } \theta>p^*,\\ 0 & \text{if } \theta<p^*.\end{cases}$$
--   Then this mechanism maximizes the seller's expected revenue $\int_{\underline\theta}^{\bar\theta}t(\theta)f(\theta)\,d\theta$ among **all** incentive-compatible, individually rational direct mechanisms $(q',t')$, including randomized ones with $q'(\theta)\in[0,1]$ arbitrary.
--
--   Precisely: (1) the version with $q(p^*)=1$, $t(p^*)=p^*$ is incentive-compatible and (2) individually rational; and (3) every incentive-compatible, individually rational direct mechanism that coincides with the displayed $(q,t)$ at every $\theta\neq p^*$ has expected revenue at least that of every incentive-compatible, individually rational direct mechanism.
--
--   The seller cannot do better than quoting a single take-it-or-leave-it price, even though she may commit to any lottery-based or indirect selling procedure (by the revelation principle, Proposition 2.1).
--
--   **Formalization Note** The book leaves $q(p^*)$ and $t(p^*)$ unspecified; clause (3) covers every choice of these values that keeps the mechanism incentive-compatible and individually rational, and clauses (1)–(2) show that such a choice exists. No measurability or integrability hypotheses are placed on the competing mechanisms: incentive compatibility makes their payment rules bounded and measurable (Proposition 2.2), so each expected revenue is a genuine integral.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.17, Proposition 2.5

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.5**, p.17 (the goal). Suppose `p* ∈ argmax_{p ∈ [θ̲, θ̄]} p (1 − F(p))`. The
posted-price mechanism — `q(θ) = 1`, `t(θ) = p*` if `θ > p*`, and `q(θ) = 0`, `t(θ) = 0` if
`θ < p*` — maximizes the seller's expected revenue among all incentive-compatible, individually
rational direct mechanisms.

Stated as: (1) the version with `q(p*) = 1`, `t(p*) = p*` is incentive-compatible and
(2) individually rational; (3) every incentive-compatible, individually rational direct mechanism
that agrees with the displayed `q` and `t` at every `θ ≠ p*` has expected revenue at least that of
every incentive-compatible, individually rational direct mechanism (whose `q` may take any value
in `[0, 1]`, i.e. randomized mechanisms are included). -/
theorem posted_price_optimal {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (postedPrice θlo θhi pstar).IsIC ∧ (postedPrice θlo θhi pstar).IsIR ∧
      ∀ m : DirectMechanism θlo θhi,
        (∀ θ ∈ Set.Icc θlo θhi, θ ≠ pstar →
          m.q θ = (if pstar < θ then 1 else 0) ∧ m.t θ = (if pstar < θ then pstar else 0)) →
        m.IsIC → m.IsIR →
        ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
          expectedRevenue D m' ≤ expectedRevenue D m := by sorry

end MechanismDesign.Screening
