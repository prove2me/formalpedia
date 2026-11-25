-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:06.870021+00:00
-- url     : https://prove2.me/theorems/ee5f0b4d-a962-45a5-9367-87579d86e1bb
-- title:
--   Additive Function: g add
-- statement:
--   The Additive Function construction uses the g add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L400-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean#L400-L417

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

theorem GroundTheory.ProfCoh.AdditiveFunction.g_add {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (f : A →+ B)
    (h : B →+ C) (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a)
    (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) (hf : Function.Injective f)
    (hfh : Function.Exact f h) (hh : Function.Surjective h)
    [Finite (ModN A l)] [Finite (TorsN A l)] [Finite (ModN C l)] [Finite (TorsN C l)] :
    d.g B = d.g A + d.g C := by sorry
