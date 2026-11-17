-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_removable_chart_current
-- name    : HodgeComputer.FourPlusTwoResidual.removable_chart_current
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:22.170195+00:00
-- url     : https://prove2.me/theorems/8f50bf64-18d6-4e79-a5ef-fd0b8436daa0
-- title:
--   Removable base-chart current cancellation of the t^6 term for four-plus-two-residual
-- statement:
--   Let $K$ be a field of characteristic zero equipped with commuting derivations $D_t, D_r, D_s : \operatorname{Der}_{\mathbb{Z}}(K,K)$, and let $P(t) = p_0 + p_1 t^2 + p_2 t^4 + p_3 t^6$ where $D_t(p_j) = 0$, $D_s(p_0) = 0$, and $D_r(p_3) = 0$.
--
--   For any base vector field of the form $(q_t, q_r, q_s) = (a_0 t,\, b,\, p_3 c)$ with $D_t a_0 = 0$ and $3 a_0 = D_r b + p_3 D_s c + \tfrac{1}{3}(D_s p_3)\,c$, the $t^6$ term of $-(P\,\operatorname{div}q - \tfrac{2}{3} q(P))$ cancels identically, leaving
--
--   $$-\Bigl(P\,\operatorname{div}q - \tfrac{2}{3}\,q(P)\Bigr) = s_0 + s_1 t^2 + s_2 t^4.$$
-- source:
--   Hodge Computer research (FourPlusTwoCubicChart.lean, removable_chart_current)

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.FourPlusTwoResidual.removable_chart_current
    {K : Type*} [Field K] [CharZero K]
    (Dt Dr Ds : Derivation ℤ K K)
    (p : Fin 4 → K) (t b c : K)
    (ht_t : Dt t = 1) (ht_r : Dr t = 0) (ht_s : Ds t = 0)
    (hp_t : ∀ j : Fin 4, Dt (p j) = 0)
    (hp0_s : Ds (p 0) = 0) (hp3_r : Dr (p 3) = 0)
    (ha0_t : Dt ((1 / 3 : K) * (Dr b + p 3 * Ds c + (1 / 3 : K) * Ds (p 3) * c)) = 0) :
    let a0 : K := (1 / 3 : K) * (Dr b + p 3 * Ds c + (1 / 3 : K) * Ds (p 3) * c);
    let qt : K := a0 * t;
    let qr : K := b;
    let qs : K := p 3 * c;
    let Pt : K := p 0 + p 1 * t ^ 2 + p 2 * t ^ 4 + p 3 * t ^ 6;
    let divq := Dt qt + Dr qr + Ds qs;
    let qP := qt * Dt Pt + qr * Dr Pt + qs * Ds Pt;
    let s0 := (2 / 3 : K) * b * Dr (p 0) - (4 / 3 : K) * Dr b * p 0 -
      (10 / 9 : K) * c * p 0 * Ds (p 3) - (4 / 3 : K) * Ds c * p 0 * p 3;
    let s1 := (2 / 3 : K) * b * Dr (p 1) - (8 / 9 : K) * Dr b * p 1 -
      (26 / 27 : K) * c * p 1 * Ds (p 3) + (2 / 3 : K) * c * Ds (p 1) * p 3 -
      (8 / 9 : K) * Ds c * p 1 * p 3;
    let s2 := (2 / 3 : K) * b * Dr (p 2) - (4 / 9 : K) * Dr b * p 2 -
      (22 / 27 : K) * c * p 2 * Ds (p 3) + (2 / 3 : K) * c * Ds (p 2) * p 3 -
      (4 / 9 : K) * Ds c * p 2 * p 3;
    -(Pt * divq - (2 / 3 : K) * qP) = s0 + s1 * t ^ 2 + s2 * t ^ 4 := by sorry
