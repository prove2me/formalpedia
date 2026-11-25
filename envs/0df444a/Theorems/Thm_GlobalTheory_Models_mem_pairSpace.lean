-- Prove2me | Theorems.Thm_GlobalTheory_Models_mem_pairSpace
-- name    : GlobalTheory.Models.mem_pairSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:18.515718+00:00
-- url     : https://prove2.me/theorems/80aa06ea-c385-5728-bbbe-bc6dae26843f
-- title:
--   Models: mem pair Space
-- statement:
--   The Models construction uses the mem pair Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L216-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L216-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}

theorem GlobalTheory.Models.mem_pairSpace {m r : ℕ} {D : ModPG R n (Vc k m)} {Dt : TopData n r} {N : Lats k n m}
    {b g : ZMod n → Vc k m} : (b, g) ∈ pairSpace D Dt N ↔ InZZ D Dt N b g := by sorry
