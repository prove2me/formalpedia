-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_prod
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:21.353807+00:00
-- url     : https://prove2.me/theorems/b838df90-f8bb-4dc3-8cb1-d9535f436531
-- title:
--   Additive Function: to Fun prod
-- statement:
--   The Additive Function construction uses the to Fun prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
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

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_prod {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y] (ρ : Representation (ZMod l) Γ X)
    (σ : Representation (ZMod l) Γ Y) :
    d.toFun (X × Y) (ρ.prod σ) = d.toFun X ρ + d.toFun Y σ := by sorry
