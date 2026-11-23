-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_unrTorus_apply
-- name    : GlobalTheory.LGrp.unrTorus_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:26.735319+00:00
-- url     : https://prove2.me/theorems/fc7d01aa-2bd0-41db-921d-d2173223d5d2
-- title:
--   LGrp: unr Torus apply
-- statement:
--   The LGrp construction uses the unr Torus apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L659-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L659-L661

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
open WithZero

theorem GlobalTheory.LGrp.unrTorus_apply {k n : Type} [Field k] [Fintype n] (v : k →*₀ WithZero (Multiplicative ℤ)) (α : n → ℂˣ)
    (t : n → kˣ) : unrTorus v α t = ∏ i, unrChar v (α i) (t i) := by sorry
