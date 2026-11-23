-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_modulus_measure
-- name    : GlobalTheory.LGrp.modulus_measure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:58.250637+00:00
-- url     : https://prove2.me/theorems/94e2b4a6-fdc3-419a-b70d-9b4016c535e5
-- title:
--   LGrp: modulus measure
-- statement:
--   The LGrp construction uses the modulus measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L195-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L195-L204

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
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

theorem GlobalTheory.LGrp.modulus_measure (U : Subgroup G) (hU : IsClosed (U : Set G)) [MeasurableSpace U] [BorelSpace U]
    (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular] (g : Subgroup.normalizer (U : Set G)) (X : Set U) :
    μ (conjAut U g '' X) = modulus U hU g * μ X := by sorry
