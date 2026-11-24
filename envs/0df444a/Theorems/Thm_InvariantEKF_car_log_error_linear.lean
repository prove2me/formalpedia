-- Prove2me | Theorems.Thm_InvariantEKF_car_log_error_linear
-- name    : InvariantEKF.car_log_error_linear
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:16:13.320784+00:00
-- url     : https://prove2.me/theorems/fcf88d63-8e5e-471d-81f2-ab66c63aa47d
-- title:
--   Proposition 1 (as proved): the logarithmic error of the car obeys a linear autonomous equation
-- statement:
--   Consider two trajectories $(\theta_t,x^1_t,x^2_t)$ and $(\bar\theta_t,\bar x^1_t,\bar x^2_t)$, $t\ge0$, of the non-holonomic car with the same inputs:
--
--   $$\dot\theta=\omega_t,\qquad\dot x^1=\cos(\theta_t)u_t,\qquad\dot x^2=\sin(\theta_t)u_t.$$
--
--   Let $\xi_t=\big(\Delta\theta_t,\ \tfrac12\Delta\theta_t\,[a(\Delta\theta_t)I_2-J_2]\,R(-\bar\theta_t)(X_t-\bar X_t)\big)$ be the error (2), where $\Delta\theta=\theta-\bar\theta$ and $a(s)=\sin s/(1-\cos s)$. The factor $\tfrac12 s\,a(s)$ is taken equal to its limit $1$ at $s=0$. Assume that either $\Delta\theta_0=0$ or $\cos\Delta\theta_0\ne1$. Then for every $t\ge0$,
--
--   $$\frac{d}{dt}\xi_t=\begin{pmatrix}0&0&0\\0&0&\omega_t\\u_t&-\omega_t&0\end{pmatrix}\xi_t .$$
--
--   So a non-linear function of the two trajectories obeys a linear, state-independent equation.
--
--   **Formalization Note** The paper prints the entry $-u_t$ in the bottom-left corner. That is a sign error: the proof's line $\delta\theta_tJ_2(u_t,0)^T$ equals $\delta\theta_t(0,u_t)^T$, not $\delta\theta_t(0,-u_t)^T$. The matrix $A_t$ of Section 4.2.3 also has $+v_t$ there, and a numerical check confirms $+u_t$. The error (2) is undefined when $\Delta\theta\in2\pi\mathbb Z\setminus\{0\}$, so that case is excluded. $\Delta\theta$ is constant in time, so it suffices to state the hypothesis at $t=0$. Derivatives at $t=0$ are one-sided.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Section 2.1, Proposition 1, eqs. (2)-(3), p. 4

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem car_log_error_linear (u ω θ x1 x2 θbar xbar1 xbar2 : ℝ → ℝ)
    (hθ : ∀ t, 0 ≤ t → HasDerivWithinAt θ (ω t) (Set.Ici 0) t)
    (hx1 : ∀ t, 0 ≤ t → HasDerivWithinAt x1 (Real.cos (θ t) * u t) (Set.Ici 0) t)
    (hx2 : ∀ t, 0 ≤ t → HasDerivWithinAt x2 (Real.sin (θ t) * u t) (Set.Ici 0) t)
    (hθbar : ∀ t, 0 ≤ t → HasDerivWithinAt θbar (ω t) (Set.Ici 0) t)
    (hxbar1 : ∀ t, 0 ≤ t → HasDerivWithinAt xbar1 (Real.cos (θbar t) * u t) (Set.Ici 0) t)
    (hxbar2 : ∀ t, 0 ≤ t → HasDerivWithinAt xbar2 (Real.sin (θbar t) * u t) (Set.Ici 0) t)
    (hdef : θ 0 - θbar 0 = 0 ∨ Real.cos (θ 0 - θbar 0) ≠ 1) :
    ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun s => carLogError (θ s) (x1 s) (x2 s) (θbar s) (xbar1 s) (xbar2 s))
        (carErrorMatrix (u t) (ω t) *ᵥ carLogError (θ t) (x1 t) (x2 t) (θbar t) (xbar1 t) (xbar2 t))
        (Set.Ici 0) t := by sorry

end InvariantEKF
