-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_zero_of_subsingleton
-- name    : GroundTheory.ProfCoh.AdditiveFunction.toFun_eq_zero_of_subsingleton
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:23.406559+00:00
-- url     : https://prove2.me/theorems/053462a2-7fe2-4137-8491-7bbbe507bc5b
-- title:
--   Additive Function: to Fun eq zero of subsingleton
-- statement:
--   The Additive Function construction uses the to Fun eq zero of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L44-L50

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

theorem GroundTheory.ProfCoh.AdditiveFunction.toFun_eq_zero_of_subsingleton [Subsingleton X] (ρ : Representation (ZMod l) Γ X) :
    d.toFun X ρ = 0 := by sorry
