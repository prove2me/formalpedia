-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_IsMatrixCoeff_checkFun
-- name    : GlobalTheory.LGrp.IsMatrixCoeff.checkFun
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:44.261334+00:00
-- url     : https://prove2.me/theorems/8eeee97d-cb3d-59d7-a39c-ca226df27717
-- title:
--   Is Matrix Coeff: check Fun
-- statement:
--   The Is Matrix Coeff construction uses the check Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1129-L1136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1129-L1136

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
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.LGrp.IsMatrixCoeff.checkFun {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {c : G → ℂ} (h : IsMatrixCoeff ρ c) :
    IsMatrixCoeff (smoothDual ρ) (checkFun c) := by sorry
