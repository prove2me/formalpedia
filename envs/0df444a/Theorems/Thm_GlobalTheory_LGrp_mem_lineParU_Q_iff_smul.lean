-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_Q_iff_smul
-- name    : GlobalTheory.LGrp.mem_lineParU_Q_iff_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:42.179363+00:00
-- url     : https://prove2.me/theorems/dc2fcc08-9d04-41d4-9919-0ac3ae2f0b56
-- title:
--   LGrp: mem line Par U Q iff smul
-- statement:
--   The LGrp construction uses the mem line Par U Q iff smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1503-L1512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1503-L1512

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

theorem GlobalTheory.LGrp.mem_lineParU_Q_iff_smul (g : GU σ (n + 2)) :
    g ∈ (lineParU σ hσ hc n).Q ↔ ∃ a : L, g.1.val *ᵥ Pi.single 0 1 = a • Pi.single 0 1 := by sorry
