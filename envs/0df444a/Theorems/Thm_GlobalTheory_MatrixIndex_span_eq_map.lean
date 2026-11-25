-- Prove2me | Theorems.Thm_GlobalTheory_MatrixIndex_span_eq_map
-- name    : GlobalTheory.MatrixIndex.span_eq_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:29.261747+00:00
-- url     : https://prove2.me/theorems/ddd130c7-9cb6-51c9-95b3-8e9f13924ca9
-- title:
--   Matrix Index: span eq map
-- statement:
--   The Matrix Index construction uses the span eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanEqMap.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanEqMap.lean#L81-L93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanEqMap
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
open GlobalTheory GlobalTheory.MatrixIndex
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.MatrixIndex.span_eq_map (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by sorry
