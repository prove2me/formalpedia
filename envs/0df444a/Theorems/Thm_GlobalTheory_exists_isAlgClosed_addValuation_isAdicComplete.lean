-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAlgClosed_addValuation_isAdicComplete
-- name    : GlobalTheory.exists_isAlgClosed_addValuation_isAdicComplete
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:01.037505+00:00
-- url     : https://prove2.me/theorems/6932a38e-da3c-5a64-a1fc-3bdeb71a8e35
-- title:
--   Global Theory: exists is Alg Closed add Valuation is Adic Complete
-- statement:
--   The Global Theory construction uses the exists is Alg Closed add Valuation is Adic Complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L64-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIsAlgClosedAddValuationIsAdicComplete.lean#L64-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIsAlgClosedAddValuationIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal

theorem GlobalTheory.exists_isAlgClosed_addValuation_isAdicComplete :
    ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [CharZero F₀] (v₀ : AddValuation F₀ (WithTop ℚ))
      (p : ℕ), p.Prime → 0 < v₀ (p : F₀) →
      ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (e : F₀ →+* F)
        (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
        IsAdicComplete (Ideal.span {(p : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v)})
          (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by sorry
