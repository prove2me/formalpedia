-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_ratio_chart_t4_witness
-- name    : HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:49:13.802466+00:00
-- url     : https://prove2.me/theorems/df7f7e21-1949-4a10-b778-9813179e6c9d
-- title:
--   Existence of a ratio-chart $t^4$ current witness (normalized push–pull output)
-- statement:
--   Let $P$ be the ratio-chart dehomogenization of the four-plus-two core and write $D_r,D_s,D_t$ for coordinate derivations on a characteristic-zero field $K$.
--
--   **Claim.** There exist $a,s,t,P,q_r,q_s,q_t\in K$ with $a,t\neq0$, derivation normalizations $D_t(t)=1$, $D_s(s)=1$, $D_r(a)=D_s(a)=D_t(a)=0$, $D_r(t)=D_s(t)=0$, and chart current $(q_r,q_s,q_t)$ satisfying
--
--   $$
--   \frac23\bigl(q_r D_r P+q_s D_s P+q_t D_t P\bigr)-P\bigl(D_r q_r+D_s q_s+D_t q_t\bigr)=t^4.
--   $$
--
--   This is the chart-side output of the Discussion #120 push–pull normalization $R=K^{-1}\alpha_A$ on the relevant character, after full finite-trace evaluation and Gauss–Manin / Hermite–Padé horizontal correction onto the source moment $e_3=(0,0,1)$. Combined with the proved `ratioChart_transport` and a clearing glue, it yields `exists_core_rational_current`.
--
--   **Formalization Note.** The displayed identity is the chart hypothesis of `ratioChart_transport`.
-- source:
--   Hodge.computer Discussion #120 (benediamond Nov 6: K=Z_*Z^* invertibility / chart currents; kmehltretter82 Nov 22: global correction), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4) := by sorry
