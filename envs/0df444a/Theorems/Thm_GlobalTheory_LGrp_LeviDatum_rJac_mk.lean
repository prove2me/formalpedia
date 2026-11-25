-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_LeviDatum_rJac_mk
-- name    : GlobalTheory.LGrp.LeviDatum.rJac_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:11.23912+00:00
-- url     : https://prove2.me/theorems/99a85a14-1432-574c-898e-4ce1b3be5dd1
-- title:
--   Levi Datum: r Jac mk
-- statement:
--   The Levi Datum construction uses the r Jac mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L349-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L349-L352

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
open GlobalTheory.LGrp.LeviDatum
variable {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M] (P : LeviDatum G M)
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.LGrp.LeviDatum.rJac_mk (π : Representation ℂ G V) (m : M) (v : V) :
    P.rJac π m (Submodule.Quotient.mk v) =
      ((P.deltaHalf (P.sQ m) : ℂ))⁻¹ • Submodule.Quotient.mk (π (P.s m) v) := by sorry
