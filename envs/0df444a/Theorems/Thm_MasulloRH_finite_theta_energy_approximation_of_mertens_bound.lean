-- Prove2me | Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
-- name    : MasulloRH.finite_theta_energy_approximation_of_mertens_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:23:08.173915+00:00
-- url     : https://prove2.me/theorems/2ff6dea5-c00e-4ec2-a48e-f6e51bba4fcb
-- title:
--   A Mertens exponent gives arbitrarily small weighted theta-approximation energy
-- statement:
--   Let $\mu$ be the arithmetic Möbius function and suppose
--
--   $$M(N)=\sum_{k=1}^N\mu(k)=O(N^\beta).$$
--
--   Fix real numbers $\beta,c,b,T$ with
--
--   $$0\le\beta,\qquad 0\le b,\qquad 0\le T,\qquad \beta<c-b,\qquad c+b<1.$$
--
--   Use the mission's actual functions
--
--   $$\theta(x)=\sum_{k\in\mathbb Z}\bigl(e^{-\pi(ke^x)^2}-3e^{-4\pi(ke^x)^2}+2e^{-16\pi(ke^x)^2}\bigr),\qquad
--   p_T(x)=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2x^2}.$$
--
--   For every $\varepsilon>0$ there are a natural number $m$, Gaussian-rational coefficients $a_1,\ldots,a_m\in\mathbb Q+i\mathbb Q$, and rational shifts $y_1,\ldots,y_m\in\mathbb Q$ such that, writing
--
--   $$r(x)=p_T(x)-\sum_{j=1}^m a_j\theta(x-y_j),$$
--
--   the weighted squared residual is integrable and
--
--   $$\int_{\mathbb R}e^{2cx+2b|x|}|r(x)|^2\,dx<\varepsilon.$$
--
--   This exposes the arbitrary-accuracy weighted-energy consequence of the mission's proved rational-translate density theorem. In particular, the target accuracy can be chosen independently of the pulse height. The Mertens estimate is an explicit hypothesis, not a conclusion; at exponents approaching $1/2$ this retains the mission's difficult arithmetic input.
--
--   **Formalization Note.** Rational complex coefficients are represented by pairs of rationals. Integrability is included alongside the strict bound, so the energy assertion is about the ordinary convergent weighted integral.
-- source:
--   Adapted from marozols, accepted Prove2Me submission 4bdbae60-2c51-4a6c-98af-6e656970db1f for MasulloRH.theta_translate_density_of_mertens_bound, https://prove2.me/theorems/16054a29-40cd-4795-8087-001dbb739caa , specifically the internal lemmas MasulloCyclic.weighted_energy_le and rational_energy_approx. This theorem exposes that argument through proved public theorem interfaces. The weighted window integral is MasulloAudit.window_mellin_evaluation_bounded (e2170362-8fa5-4c24-b4ab-c9ae6809338e); integrability is supplied by MasulloRH.finite_theta_approximation_excludes_rectangle_zeros (8481aa5d-a121-4938-8de2-17c814da37b2). It is supporting formalization for the Masullo RH mission, not a new independent proof of theta density.

import Definitions.Def_MasulloRH_GaussianThetaApproximation

set_option autoImplicit false
open Set MeasureTheory Filter Asymptotics
open scoped Topology ENNReal BigOperators
open MasulloRH.GaussianApproximation

theorem MasulloRH.finite_theta_energy_approximation_of_mertens_bound
    (β c b T ε : ℝ) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hleft : β < c-b) (hright : c+b < 1)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      (fun n : ℕ => (n:ℝ)^β)) (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let r := residual T (fun i => ((a i).1 : ℂ)+((a i).2 : ℂ)*Complex.I)
        (fun i => (y i : ℝ))
      Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖r x‖^2) ∧
        energy c b r < ε := by sorry
