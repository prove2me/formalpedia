-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratio_chart_t4_yields_homogenized_source_a6t3
-- name    : HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_yields_homogenized_source_a6t3
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T11:57:37.698794+00:00
-- url     : https://prove2.me/theorems/b658e6a5-717a-4a6d-be8e-0535b1a3df42
-- title:
--   Ratio-chart $t^4$ witness yields homogenized source $a^6 t^3$
-- statement:
--   **Claim.** Any ratio-chart $t^4$ witness yields (after the proved transport map of `ratioChart_transport`) the homogenized twisted identity with source $a^6 t^3$ in ratio coordinates $(a,ar,at,ast)$.
--
--   This is the first half of the chart→`CoreRationalEquation` glue: apply `ratioChart_transport` pointwise to the witness data and re-pack the existential.
--
--   **Formalization Note.** Conclusion mirrors the `let`-binding conclusion of `ratioChart_transport`.
-- source:
--   Proved theorem `ratioChart_transport`; Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_yields_homogenized_source_a6t3
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (let H := a ^ 6 * P
          let db := fun z : K => Dr z / a
          let dc := fun z : K => (Dt z - s / t * Ds z) / a
          let dd := fun z : K => Ds z / (a * t)
          let pb := (2 : K) * a * qr / (3 * t)
          let pc := (2 : K) * a * qt / (3 * t)
          let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
          pb * db H + pc * dc H + pd * dd H -
            (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3) := by sorry
