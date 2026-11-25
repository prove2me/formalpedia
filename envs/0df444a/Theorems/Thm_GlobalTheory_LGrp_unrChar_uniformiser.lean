-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_unrChar_uniformiser
-- name    : GlobalTheory.LGrp.unrChar_uniformiser
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:09.819723+00:00
-- url     : https://prove2.me/theorems/701f5bc3-d66c-474c-a11d-e0b35473f60a
-- title:
--   LGrp: unr Char uniformiser
-- statement:
--   The LGrp construction uses the unr Char uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L686-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L686-L701

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
open ValuativeRel
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}

theorem GlobalTheory.LGrp.unrChar_uniformiser (z : ℂˣ) (ϖ : kˣ) (h1 : valuation k (ϖ : k) < 1)
    (hmax : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (ϖ : k)) : unrChar (vZ k) z ϖ = z := by sorry
