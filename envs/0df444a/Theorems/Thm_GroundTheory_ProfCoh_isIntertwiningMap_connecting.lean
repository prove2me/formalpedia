-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isIntertwiningMap_connecting
-- name    : GroundTheory.ProfCoh.isIntertwiningMap_connecting
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:00.056419+00:00
-- url     : https://prove2.me/theorems/8fedecd4-10f8-4dd9-bc21-9306e3276100
-- title:
--   Prof Coh: is Intertwining Map connecting
-- statement:
--   The Prof Coh construction uses the is Intertwining Map connecting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L332-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L332-L341

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)

theorem GroundTheory.ProfCoh.isIntertwiningMap_connecting {n : ℕ} {f : A →+ B} {h : B →+ C}
    (hh : Function.Surjective h) (hfh : Function.Exact f h) (hf : Function.Injective f)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) :
    (torsNRep Γ C n).IsIntertwiningMap (modNRep Γ A n) (connecting hh hfh hf) := by sorry
