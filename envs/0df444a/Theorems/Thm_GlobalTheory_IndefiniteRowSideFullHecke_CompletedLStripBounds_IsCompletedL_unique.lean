-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompletedLStripBounds_IsCompletedL_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.IsCompletedL.unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:25:44.548836+00:00
-- url     : https://prove2.me/theorems/49e70013-e56b-45b9-a238-1f60a29c2217
-- title:
--   Is Completed L: unique
-- statement:
--   The Is Completed L construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.IsCompletedL.unique {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g := by sorry
