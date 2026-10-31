-- Prove2me | Theorems.Thm_JointEstimationRobustness_EstimateSupport_proposition_3
-- name    : JointEstimationRobustness.EstimateSupport.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:12:31.740059+00:00
-- url     : https://prove2.me/theorems/f6bd566b-8ee7-4e90-af68-c76468f24fc5
-- title:
--   Proposition 3 — Support of the estimate uncertainty set via the estimation metric's conjugate
-- statement:
--   Fix data $D$ and a finite parameter dimension $M$. Let $W\subseteq\bar W\subseteq\mathbb R^M$, and let $\rho(\beta)=\rho(\beta;D)$ be real valued on $\bar W$ and convex on that domain. Let $\widehat\beta\in W$ minimize $\rho$ over $W$, without any uniqueness assumption, and write $\widehat\rho=\rho(\widehat\beta)$.
--   Define
--   $$\mathcal E(r;D)=\{\beta\in W:\rho(\beta)\le\widehat\rho+r\},\quad \delta_r^*(\nu)=\sup_{\beta\in\mathcal E(r;D)}\beta^\top\nu,$$
--   $$\rho^*(v;D)=\sup_{\beta\in\bar W}\bigl(\beta^\top v-\rho(\beta)\bigr).$$
--   Proposition 3 asserts that for every $r>0$ and every ambient direction $\nu\in\mathbb R^M$,
--   $$\delta_r^*(\nu)=\inf_{\mu>0}\bigl\{(\widehat\rho+r)\mu+\mu\rho^*(\nu/\mu;D)\bigr\}.$$
--   Suprema and the infimum are extended-real values. No boundedness, closedness, compactness, equality $W=\bar W$, or attainment of the infimum is assumed.
--
--   The identity is intended to express the support of a loss-based uncertainty set through a conjugate. The printed assertion is retained unchanged in strength; finding I1 records a counterexample caused by its distinct domains. It is a statement target, not a claim of a checked proof.
--
--   Differences from the source:
--   - encoding: vectors in real M-space and transposed products → functions on Fin M and the published real dot product in reversed order; reason: finite coordinates and commutativity preserve all values, including the zero-dimensional convention.
--   - encoding: the data-dependent metric rho(beta; D) → an arbitrary ambient real function rho with D fixed and values outside Wbar unused; reason: every fixed-data instance is represented without statistical restrictions.
--   - encoding: beta-hat is an argmin over W and rho-hat is its value → membership and a universal minimum inequality, with rho-hat computed by estimateValue; reason: this expresses an attained minimum without introducing uniqueness or an independent threshold.
--   - reading: rho is convex in beta → ConvexOn over Wbar, including convexity of Wbar; reason: convexity is read on the domain used in the printed conjugate, without continuity or closedness.
--   - encoding: support, conjugate and perspective infimum may be infinite → EReal suprema and infimum, with finite real coefficients embedded before arithmetic; reason: unbounded cases retain their extended values rather than default real extrema.
--   - encoding: infimum over positive real mu and vector quotient nu/mu → infimum over the positive-real subtype and coordinatewise division; reason: the exact domain mu > 0 is retained and division by zero never occurs.
--   - reading: the support-function direction nu in (11) → every ambient vector nu; reason: (11) and its proof impose no directional constraint, and Proposition 2's parenthetical domain is local to that separate certificate.
-- source:
--   Zhu, Xie and Sim (2022), Joint Estimation and Robustness Optimization, https://doi.org/10.1287/mnsc.2020.3898, supplied artifact Proposition 3, (11), PDF/printed p. 7; standing setup pp. 4–6; proof Appendix A, p. 26. Citation basis: published, as supplied metadata.

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_ConvexDuality
import Definitions.Def_JointEstimationRobustness_EstimateSupport_Estimation

namespace JointEstimationRobustness.EstimateSupport

theorem proposition_3 {M : ℕ} (W Wbar : Set (Fin M → ℝ))
    (ρ : (Fin M → ℝ) → ℝ) (βhat : Fin M → ℝ)
    (hW : W ⊆ Wbar) (hEstimate : IsMinimizingEstimate W ρ βhat)
    (hConvex : ConvexOn ℝ Wbar ρ) (r : ℝ) (hr : 0 < r) (ν : Fin M → ℝ) :
    FenchelRobust.Counterpart.supportFun (estimateSet W ρ βhat r) ν =
      ⨅ μ : {t : ℝ // 0 < t},
        ((((estimateValue ρ βhat + r) * (μ : ℝ)) : ℝ) : EReal) +
          ((μ : ℝ) : EReal) *
            FenchelRobust.Counterpart.convexConj Wbar ρ
              (fun i => ν i / (μ : ℝ)) := by sorry

end JointEstimationRobustness.EstimateSupport
