-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_periods_polarised
-- name    : GlobalTheory.AnArc.periods_polarised
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:45.078708+00:00
-- url     : https://prove2.me/theorems/df8ab407-2058-5f12-bab5-ce43a844ef26
-- title:
--   An Arc: periods polarised
-- statement:
--   The An Arc construction uses the periods polarised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L463-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L463-L479

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.periods_polarised :
    A.EF.IsAlt ∧ Function.Bijective A.EF ∧ (∀ (a : O) x y, A.EF (a • x) y = A.EF x (star a • y)) ∧
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im →
      (A.BwMat w).PosDef ∧ Function.Injective (A.Pw w) ∧ (∀ (a : O) x, A.Pw w (a • x) = A.actV a (A.Pw w x)) ∧
      DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ ∧
      (∀ v v', starRingEnd ℂ (A.Hw w v v') = A.Hw w v' v) ∧ (∀ v, v ≠ 0 → 0 < (A.Hw w v v).re) ∧
      (∀ a b, (A.Hw w (A.Pw w a) (A.Pw w b)).im = A.EF a b) ∧
      ∀ (g : ℕ) (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (P : A.La →+ (Fin g → ℂ)), (∀ x, P x = h (A.Pw w x)) →
        Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
          ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            ∀ x y, (hermForm Hm (P x) (P y)).im = A.EF x y := by sorry
