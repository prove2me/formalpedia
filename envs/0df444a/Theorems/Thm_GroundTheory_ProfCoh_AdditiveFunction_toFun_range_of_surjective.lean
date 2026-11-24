-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_range_of_surjective
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_surjective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:32.299433+00:00
-- url     : https://prove2.me/theorems/d308a0a9-f466-4787-95e5-d654ab75082d
-- title:
--   Additive Function: to Fun range of surjective
-- statement:
--   The Additive Function construction uses the to Fun range of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L92-L97

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
omit [Finite X]

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_range_of_surjective (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) (φ : X →ₗ[ZMod l] Y) (hφ : ρ.IsIntertwiningMap σ φ)
    (hs : Function.Surjective φ) :
    d.toFun (LinearMap.range φ)
        (σ.subrepresentation _ (range_le_comap_of_isIntertwiningMap hφ)) = d.toFun Y σ := by sorry
