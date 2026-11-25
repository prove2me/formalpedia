-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratio_chart_t4_of_flat_moment_section_e3
-- name    : HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_of_flat_moment_section_e3
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T11:57:20.054704+00:00
-- url     : https://prove2.me/theorems/794a7f50-0351-5e1c-a5bf-cc62133bb9d0
-- title:
--   Flat moment section with $\mathcal{M}c=e_3$ yields a ratio-chart $t^4$ witness
-- statement:
--   **Claim.** From any Hermite–Padé / flat-basis moment section with $\sum c_j T_j=(0,0,1)$ and chart current equal to the corresponding moment combination, one obtains a ratio-chart $t^4$ witness (the hypothesis package of `ratioChart_transport`).
--
--   The transport is pure algebra: substitute the moment identities into the displayed chart divergence to conclude that the source equals $t^4$, then forget the auxiliary $(n,c,T_\bullet)$ data.
--
--   **Formalization Note.** Target type matches `exists_ratio_chart_t4_witness`.
-- source:
--   Discussion #120 global-trace architecture; WORMHOLE φ = substitute Mc=e3 into chart current, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_of_flat_moment_section_e3
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P : K)
      (n : ℕ) (c : Fin n → K) (T0 T2 T4 : Fin n → K)
      (qr qs qt : K),
      n ≠ 0 ∧
        a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (∑ j : Fin n, c j * T0 j = 0) ∧
        (∑ j : Fin n, c j * T2 j = 0) ∧
        (∑ j : Fin n, c j * T4 j = 1) ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) =
          (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4) := by sorry
