-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_twKer_charFst_le_ker
-- name    : GlobalTheory.LGrp.twKer_charFst_le_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:48.335666+00:00
-- url     : https://prove2.me/theorems/062012f6-103e-4cd8-8dfc-cfc8ec6311d2
-- title:
--   LGrp: tw Ker char Fst le ker
-- statement:
--   The LGrp construction uses the tw Ker char Fst le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1074-L1086
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1074-L1086

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

theorem GlobalTheory.LGrp.twKer_charFst_le_ker (χ : A →* ℂˣ) (ρ : Representation ℂ (A × H) V) (f : V →ₗ[ℂ] W) :
    twKer ρ (MonoidHom.inl A H).range (charFst H χ) ≤ LinearMap.ker f ↔
      ∀ a v, f (ρ (a, 1) v) = (χ a : ℂ) • f v := by sorry
