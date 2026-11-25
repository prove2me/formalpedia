-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_coinvTensor_mk
-- name    : GlobalTheory.LGrp.coinvTensor_mk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:36.948847+00:00
-- url     : https://prove2.me/theorems/f00453e9-167c-4888-965f-0898a4b8e508
-- title:
--   LGrp: coinv Tensor mk
-- statement:
--   The LGrp construction uses the coinv Tensor mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1052-L1054
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1052-L1054

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

theorem GlobalTheory.LGrp.coinvTensor_mk (ω : Representation ℂ (G × H) V) (τ : Representation ℂ G W) (h : H) (v : V) (w : W) :
    coinvTensor ω τ h (Submodule.Quotient.mk (v ⊗ₜ w)) = Submodule.Quotient.mk (ω (1, h) v ⊗ₜ w) := by sorry
