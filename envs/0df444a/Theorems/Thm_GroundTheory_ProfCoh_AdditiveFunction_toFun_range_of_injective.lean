-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_range_of_injective
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:43.563404+00:00
-- url     : https://prove2.me/theorems/41c1dcc8-13d8-4aad-8161-6fdee58da6fc
-- title:
--   Additive Function: to Fun range of injective
-- statement:
--   The Additive Function construction uses the to Fun range of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L80-L88

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
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_injective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hinj : Function.Injective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun X ρ := by sorry
