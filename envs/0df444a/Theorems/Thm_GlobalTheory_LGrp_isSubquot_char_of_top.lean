-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_isSubquot_char_of_top
-- name    : GlobalTheory.LGrp.isSubquot_char_of_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:56.656174+00:00
-- url     : https://prove2.me/theorems/90628653-5e39-4154-b27e-80d0dcf0319a
-- title:
--   LGrp: is Subquot char of top
-- statement:
--   The LGrp construction uses the is Subquot char of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L898-L922
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LineOppositeParabolicUnitaryLeviSectionEq.lean#L898-L922

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

theorem GlobalTheory.LGrp.isSubquot_char_of_top {G M : Type} [Group G] [TopologicalSpace G] [Group M] [TopologicalSpace M]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T1Space M] (P : LeviDatum G M) (hU : P.U = ⊥) (χ : M →* ℂˣ)
    (ω : G →* ℂˣ) (hQ : ∀ g, g ∈ P.Q) (hω : ∀ q : P.Q, ω q = χ (P.p q)) (hs : IsSmooth (charRep ω)) :
    IsSubquot (charRep ω) (P.nInd (charRep χ)) := by sorry
