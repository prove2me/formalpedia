-- Prove2me | Theorems.Thm_GlobalTheory_HL_relVol_eq_mul_of_le
-- name    : GlobalTheory.HL.relVol_eq_mul_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:37.571573+00:00
-- url     : https://prove2.me/theorems/4041e6c3-da64-4ac6-822e-172d9b52feb6
-- title:
--   HL: rel Vol eq mul of le
-- statement:
--   The HL construction uses the rel Vol eq mul of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L50-L71

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.relVol_eq_mul_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    relVol W0 A = (A'.relIndex A : ℝ) * relVol W0 A' := by sorry
