-- Prove2me | Theorems.Thm_FrieszDUE_PIE_near_min_set_pos_measure_47
-- name    : FrieszDUE.PIE.near_min_set_pos_measure_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:56.652698+00:00
-- url     : https://prove2.me/theorems/63223a67-574e-45bf-a71d-b993c7abb738
-- title:
--   (47), p. 188 — for a route q attaining μ_kl(h*), T_q(ε) = {t: C_q(t, h*) < μ*_kl + ε} has positive measure
-- statement:
--   In the setting of the PIE model, let $T>0$, let $h^*$ be a density vector whose costs $C_p(\cdot,h^*)$ are nonnegative on $[0,T]$ and measurable, and write $\mu^*_{kl}=\mu_{kl}(h^*)$. Let $q\in P_{kl}$ be a route with $\mu_q(h^*)=\mu_{kl}(h^*)$. Then for every $\varepsilon>0$ the set
--
--   $$T_q(\varepsilon)=\{t\in[0,T]: C_q(t,h^*)<\mu^*_{kl}+\varepsilon\}\qquad(47)$$
--
--   has positive measure.
--
--   This is the defining property of the essential infimum (12) applied to the cheapest route $q$; it supplies the set onto which flow is shifted in the sufficiency half of Theorem 2.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 188, proof of Theorem 2 part ii, (47), with (12) and (14)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part ii, (47), p. 188. -/
theorem near_min_set_pos_measure_47 {P W : Type*}
    (T : ℝ) (hT : 0 < T) (od : P → W) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t hs)
    (hC_meas : ∀ p, AEMeasurable (fun t => C p t hs) (ν T))
    (q : P) (hq : muPath T C hs q = muOD T od C hs (od q)) (ε : ℝ) (hε : 0 < ε) :
    0 < ν T {t | C q t hs < muOD T od C hs (od q) + ε} := by sorry

end FrieszDUE.PIE
