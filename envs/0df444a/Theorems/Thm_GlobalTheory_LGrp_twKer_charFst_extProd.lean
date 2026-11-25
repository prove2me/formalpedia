-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_twKer_charFst_extProd
-- name    : GlobalTheory.LGrp.twKer_charFst_extProd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:30.341866+00:00
-- url     : https://prove2.me/theorems/ad3dc190-5398-4030-95d6-cf4aa8cfc2e5
-- title:
--   LGrp: tw Ker char Fst ext Prod
-- statement:
--   The LGrp construction uses the tw Ker char Fst ext Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1107-L1125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1107-L1125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {A G H V W : Type} [Group A] [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.LGrp.twKer_charFst_extProd (χ χ' : A →* ℂˣ) (π : Representation ℂ H W) :
    (χ = χ' → twKer (extProd (charRep χ') π) (MonoidHom.inl A H).range (charFst H χ) = ⊥) ∧
      (χ ≠ χ' → twKer (extProd (charRep χ') π) (MonoidHom.inl A H).range (charFst H χ) = ⊤) := by sorry
