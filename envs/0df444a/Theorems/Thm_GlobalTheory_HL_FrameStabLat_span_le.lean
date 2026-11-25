-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStabLat_span_le
-- name    : GlobalTheory.HL.FrameStabLat.span_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:08:21.299821+00:00
-- url     : https://prove2.me/theorems/cdf84f57-d472-422f-98e9-4f8b5a42a4de
-- title:
--   Frame Stab Lat: span le
-- statement:
--   The Frame Stab Lat construction uses the span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L56-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)

theorem GlobalTheory.HL.FrameStabLat.span_le {ι : Type} (g : ι → V) {x : V} (hx : x ∈ Submodule.span O (Set.range g)) :
    x ∈ Submodule.span E (Set.range g) := by sorry
