-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_invariantsTensor_apply
-- name    : GroundTheory.ProfCoh.AdditiveFunction.invariantsTensor_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:35.075804+00:00
-- url     : https://prove2.me/theorems/df13e8d2-4734-4363-b54c-635571c4b479
-- title:
--   Additive Function: invariants Tensor apply
-- statement:
--   The Additive Function construction uses the invariants Tensor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveInvariants.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveInvariants.lean#L96-L101

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
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
universe u v w
open Representation TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction

theorem GroundTheory.ProfCoh.AdditiveFunction.invariantsTensor_apply (l : ℕ) [Fact l.Prime] (Γ : Type v) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type w} [AddCommGroup N] [Module (ZMod l) N]
    [Module.Finite (ZMod l) N] (σ : Representation (ZMod l) Γ N) (X : Type u) [AddCommGroup X]
    [Module (ZMod l) X] [Finite X] (ρ : Representation (ZMod l) Γ X) :
    (invariantsTensor.{u} l Γ hΓ σ).toFun X ρ = Module.finrank (ZMod l) (ρ.tprod σ).invariants := by sorry
