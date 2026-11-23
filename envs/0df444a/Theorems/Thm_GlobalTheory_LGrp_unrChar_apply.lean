-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_unrChar_apply
-- name    : GlobalTheory.LGrp.unrChar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:50.783163+00:00
-- url     : https://prove2.me/theorems/c904dcf0-d022-47d9-b1cc-7d4f47b7fd32
-- title:
--   LGrp: unr Char apply
-- statement:
--   The LGrp construction uses the unr Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L652-L653
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L652-L653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_SmGL_unrChar_apply

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
open WithZero

theorem GlobalTheory.LGrp.unrChar_apply {k : Type} [Field k] (v : k →*₀ WithZero (Multiplicative ℤ)) (z : ℂˣ) (x : kˣ) :
    unrChar v z x = z ^ (-log (v x)) := by sorry
