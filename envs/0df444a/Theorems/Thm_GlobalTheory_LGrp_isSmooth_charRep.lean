-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_isSmooth_charRep
-- name    : GlobalTheory.LGrp.isSmooth_charRep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:00.630562+00:00
-- url     : https://prove2.me/theorems/ccdbc09a-fb42-4e1b-a6a3-efc18e9a5865
-- title:
--   LGrp: is Smooth char Rep
-- statement:
--   The LGrp construction uses the is Smooth char Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L924-L932
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L924-L932

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

theorem GlobalTheory.LGrp.isSmooth_charRep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ω : G →* ℂˣ)
    (h : {g | ω g = 1} ∈ nhds (1 : G)) : IsSmooth (charRep ω) := by sorry
