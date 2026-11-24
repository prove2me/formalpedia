-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_frameLat_mul_le
-- name    : GlobalTheory.SgGlob.frameLat_mul_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:48.492774+00:00
-- url     : https://prove2.me/theorems/bb17d6dc-219b-48b0-98cb-0dc709b92aa8
-- title:
--   Sg Glob: frame Lat mul le
-- statement:
--   The Sg Glob construction uses the frame Lat mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L349-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L349-L366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {n r : ℕ}

theorem GlobalTheory.SgGlob.frameLat_mul_le (P : Matrix (Fin n) (Fin (r + 1)) E) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hu : u ∈ UO E r) : frameLat (P * u) ≤ frameLat P := by sorry
