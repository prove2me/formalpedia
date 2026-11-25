-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_lineParUOp_p
-- name    : GlobalTheory.LGrp.lineParUOp_p
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:17.136159+00:00
-- url     : https://prove2.me/theorems/48c95574-3400-54e8-94fb-97970f9fe311
-- title:
--   LGrp: line Par UOp p
-- statement:
--   The LGrp construction uses the line Par UOp p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1458-L1461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1458-L1461

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
open Formalism.UG
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)

theorem GlobalTheory.LGrp.lineParUOp_p (q : (lineParUOp σ hσ hc n).Q) :
    (((lineParUOp σ hσ hc n).p q).1 : L) = q.1.1.val 0 0 ∧
      ∀ i j, ((lineParUOp σ hσ hc n).p q).2.1.val i j = q.1.1.val (midIdx i) (midIdx j) := by sorry
