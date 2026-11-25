-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_rational_of_homogenized_chart_source_a6t3
-- name    : HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T11:57:32.991115+00:00
-- url     : https://prove2.me/theorems/acfd6fde-e95c-4fc5-9f2a-7c3fbae5206b
-- title:
--   Homogenized chart source $a^6 t^3$ clears to a `CoreRationalEquation`
-- statement:
--   **Claim.** From a homogenized chart identity with source $a^6 t^3$, there exist a fraction field of $\mathbb{C}[x_0,x_1,y_0,y_1]$, coordinate derivations extending $\partial_i$, and a rational vector field $v$ satisfying `CoreRationalEquation` (source $x_0^3 y_0^3$).
--
--   The transport includes: identifying $a^3 c^3$ with the physical source under ratio coordinates, embedding into a fraction ring, and applying exact chart-transition / boundary principal-part corrections (dossier Lemmas L7–L8).
--
--   **Formalization Note.** Target type matches `exists_core_rational_current`.
-- source:
--   Discussion #120 boundary correction + density transformation; WORMHOLE φ = chart-clearing, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
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
            (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by sorry
