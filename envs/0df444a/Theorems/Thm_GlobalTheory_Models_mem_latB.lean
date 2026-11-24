-- Prove2me | Theorems.Thm_GlobalTheory_Models_mem_latB
-- name    : GlobalTheory.Models.mem_latB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:21.0933+00:00
-- url     : https://prove2.me/theorems/4e0b1f46-a457-4713-a0ed-88eee93fe3ab
-- title:
--   Models: mem lat B
-- statement:
--   The Models construction uses the mem lat B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L234-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L234-L236

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

theorem GlobalTheory.Models.mem_latB {m : ℕ} {D : ModPG R n (Vc k m)} {N : Lats k n m} {p : (ZMod n → Vc k m) × (ZMod n → Vc k m)} :
    p ∈ latB D N ↔ ∃ x : ZMod n → Vc k m, (∀ i, x i ∈ N i) ∧ herrD D x = p := by sorry
