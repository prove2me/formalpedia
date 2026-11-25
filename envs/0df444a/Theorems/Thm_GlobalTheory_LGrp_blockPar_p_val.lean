-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_blockPar_p_val
-- name    : GlobalTheory.LGrp.blockPar_p_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:47.897731+00:00
-- url     : https://prove2.me/theorems/c5bb55ea-ca83-4be5-b4ba-a3187e25e953
-- title:
--   LGrp: block Par p val
-- statement:
--   The LGrp construction uses the block Par p val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L624-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L624-L625

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
variable {k n α : Type} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]
variable [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
variable {a d : Type} [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d]

theorem GlobalTheory.LGrp.blockPar_p_val (q : (blockPar k a d).Q) :
    ((blockPar k a d).p q).1.val = q.1.val.toBlocks₁₁ ∧ ((blockPar k a d).p q).2.val = q.1.val.toBlocks₂₂ := by sorry
