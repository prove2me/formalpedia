-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameOnto_hf_spanTo
-- name    : GlobalTheory.HL.FrameOnto.hf_spanTo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:31.796297+00:00
-- url     : https://prove2.me/theorems/f9d994fb-5879-4c06-923f-f4fca7acf66d
-- title:
--   Frame Onto: hf span To
-- statement:
--   The Frame Onto construction uses the hf span To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToLePerp.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToLePerp.lean#L32-L38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.FrameOnto.hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by sorry
