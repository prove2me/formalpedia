-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_tensorRep_apply
-- name    : GroundTheory.ProfCoh.AdditiveFunction.tensorRep_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:50.064368+00:00
-- url     : https://prove2.me/theorems/39cc45b9-6b91-47ff-9b63-d66d3585020b
-- title:
--   Additive Function: tensor Rep apply
-- statement:
--   The Additive Function construction uses the tensor Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinDefs.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinDefs.lean#L83-L88

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinDefs
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
open Representation
open scoped TensorProduct
universe u v
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ]

theorem GroundTheory.ProfCoh.AdditiveFunction.tensorRep_apply [Fact l.Prime] (d : AdditiveFunction.{u} l Γ) {N : Type u}
    [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N)
    (W : Type u) [AddCommGroup W] [Module (ZMod l) W] [Finite W]
    (ρ : Representation (ZMod l) Γ W) [Finite (W ⊗[ZMod l] N)] :
    (d.tensorRep σ).toFun W ρ = d.toFun (W ⊗[ZMod l] N) (ρ.tprod σ) := by sorry
