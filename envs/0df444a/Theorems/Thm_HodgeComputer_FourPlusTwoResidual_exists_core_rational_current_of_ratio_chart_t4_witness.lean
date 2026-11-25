-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_current_of_ratio_chart_t4_witness
-- name    : HodgeComputer.FourPlusTwoResidual.exists_core_rational_current_of_ratio_chart_t4_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:49:20.020518+00:00
-- url     : https://prove2.me/theorems/d4c1588b-c876-4d81-85e7-3db508ae888e
-- title:
--   Ratio-chart $t^4$ witness implies a four-variable `CoreRationalEquation`
-- statement:
--   **Claim.** Any ratio-chart $t^4$ witness (the hypothesis package of `ratioChart_transport`) produces a fraction field $K$ of $\mathbb{C}[x_0,x_1,y_0,y_1]$, coordinate derivations $\delta_i$ extending $\partial_i$, and a rational vector field $v\in K^4$ satisfying `CoreRationalEquation δ v`, i.e.
--
--   $$
--   \sum_{i=0}^3 v_i\,\delta_i(H)-\frac32 H\sum_{i=0}^3\delta_i(v_i)=x_0^3 y_0^3.
--   $$
--
--   The map is mathematical transport, not analogy: apply the proved identity `ratioChart_transport` in ratio coordinates $(a,ar,at,ast)$, rescale by the Euler/homogenization factor relating $a^6 t^3$ to the physical source $A$, and clear into a fraction ring of the four-variable polynomial ring (including chart-transition / boundary principal-part corrections as needed).
--
--   **Formalization Note.** Target type matches `exists_core_rational_current`.
-- source:
--   Hodge.computer Discussion #120; proved lemma `ratioChart_transport`; WORMHOLE φ = chart-transport then fraction-ring clearing, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_core_rational_current_of_ratio_chart_t4_witness
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by sorry
