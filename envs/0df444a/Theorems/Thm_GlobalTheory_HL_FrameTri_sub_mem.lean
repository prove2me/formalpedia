-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem
-- name    : GlobalTheory.HL.FrameTri.sub_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:26.972892+00:00
-- url     : https://prove2.me/theorems/5dc66c95-bc42-4153-afe6-03e9cb37263f
-- title:
--   Frame Tri: sub mem
-- statement:
--   The Frame Tri construction uses the sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L101-L107

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTri
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include hg

theorem GlobalTheory.HL.FrameTri.sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) :
    n (g i) - g i ∈ S.spanTo g i := by sorry
