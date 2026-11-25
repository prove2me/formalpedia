-- Prove2me | Theorems.Thm_GlobalTheory_NB_TypedOnto_jumps_width
-- name    : GlobalTheory.NB.TypedOnto.jumps_width
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:12.626271+00:00
-- url     : https://prove2.me/theorems/e7343cd5-cf43-58bd-90f0-ce26c26c17a2
-- title:
--   Typed Onto: jumps width
-- statement:
--   The Typed Onto construction uses the jumps width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L206-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L206-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}

theorem GlobalTheory.NB.TypedOnto.jumps_width {up : ZMod n → Fin R.e → Bool} {b : ZMod n → Fin R.e → ℕ}
    {Sn η m h : ℕ} (H : TypedOnto F up b Sn η m h) (i : ZMod n) (τ : Fin R.e) :
    S₁.JumpsIn i τ (Set.Icc (-((if up i τ then η else b i τ + Sn : ℕ) : ℤ))
      ((if up i τ then b i τ + Sn else η : ℕ) : ℤ)) := by sorry
