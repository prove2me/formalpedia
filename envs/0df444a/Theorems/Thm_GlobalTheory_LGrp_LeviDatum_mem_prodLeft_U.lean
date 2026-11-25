-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_LeviDatum_mem_prodLeft_U
-- name    : GlobalTheory.LGrp.LeviDatum.mem_prodLeft_U
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:50.640339+00:00
-- url     : https://prove2.me/theorems/2b51e9c0-30fc-5b2c-a1fb-4dfac9fe5fb2
-- title:
--   Levi Datum: mem prod Left U
-- statement:
--   The Levi Datum construction uses the mem prod Left U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1158-L1161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L1158-L1161

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

theorem GlobalTheory.LGrp.LeviDatum.mem_prodLeft_U (H : Type) [Group H] [TopologicalSpace H] (g : H × G) :
    g ∈ (P.prodLeft H).U ↔ g.1 = 1 ∧ g.2 ∈ P.U := by sorry
