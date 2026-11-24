-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_mem_lineParU_U
-- name    : GlobalTheory.LGrp.mem_lineParU_U
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:02.136133+00:00
-- url     : https://prove2.me/theorems/3898fbe1-6dbd-480a-bcc4-88f52c5fef03
-- title:
--   LGrp: mem line Par U U
-- statement:
--   The LGrp construction uses the mem line Par U U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1514-L1526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1514-L1526

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

theorem GlobalTheory.LGrp.mem_lineParU_U (g : GU σ (n + 2)) :
    g ∈ (lineParU σ hσ hc n).U ↔ (∀ i, i ≠ 0 → g.1.val i 0 = 0) ∧ g.1.val 0 0 = 1 ∧
      ∀ i j, g.1.val (midIdx i) (midIdx j) = (1 : Matrix (Fin n) (Fin n) L) i j := by sorry
