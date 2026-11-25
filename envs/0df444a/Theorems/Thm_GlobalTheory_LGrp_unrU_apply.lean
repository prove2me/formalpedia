-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_unrU_apply
-- name    : GlobalTheory.LGrp.unrU_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:40.487995+00:00
-- url     : https://prove2.me/theorems/b4b9b794-123c-4e50-a41c-cce651e1e2a3
-- title:
--   LGrp: unr U apply
-- statement:
--   The LGrp construction uses the unr U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L849-L851
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L849-L851

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {α : Type} [LinearOrder α]

theorem GlobalTheory.LGrp.unrU_apply {n : ℕ} (α : Fin (n / 2) → ℂˣ) (t : Fin n → Lˣ) :
    unrU L α t = ∏ i, α i ^ ordL (t (Fin.castLE (Nat.div_le_self n 2) i) : L) := by sorry
