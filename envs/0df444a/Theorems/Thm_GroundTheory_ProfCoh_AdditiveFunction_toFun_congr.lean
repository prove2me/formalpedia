-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:26.371838+00:00
-- url     : https://prove2.me/theorems/6e506114-dd20-42f7-828f-194c9692ed64
-- title:
--   Additive Function: to Fun congr
-- statement:
--   The Additive Function construction uses the to Fun congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L52-L59

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

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_congr (ρ : Representation (ZMod l) Γ X) (σ : Representation (ZMod l) Γ Y)
    (e : X ≃ₗ[ZMod l] Y) (he : ∀ γ x, e (ρ γ x) = σ γ (e x)) :
    d.toFun X ρ = d.toFun Y σ := by sorry
