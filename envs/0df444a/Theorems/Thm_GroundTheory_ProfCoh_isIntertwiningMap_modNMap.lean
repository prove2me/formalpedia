-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isIntertwiningMap_modNMap
-- name    : GroundTheory.ProfCoh.isIntertwiningMap_modNMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:04.531728+00:00
-- url     : https://prove2.me/theorems/a5168978-8b17-4939-a4a1-2158079c4e3e
-- title:
--   Prof Coh: is Intertwining Map mod NMap
-- statement:
--   The Prof Coh construction uses the is Intertwining Map mod NMap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L326-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L326-L330

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

theorem GroundTheory.ProfCoh.isIntertwiningMap_modNMap {f : A →+ B} (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) :
    (modNRep Γ A n).IsIntertwiningMap (modNRep Γ B n) (modNMap n f) := by sorry
