-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:52.398446+00:00
-- url     : https://prove2.me/theorems/57a96425-f550-4be4-afcf-65d941f94ef4
-- title:
--   Additive Function: g eq
-- statement:
--   The Additive Function construction uses the g eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean#L129-L132

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
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

theorem GroundTheory.ProfCoh.AdditiveFunction.g_eq (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite (ModN A l)]
    [Finite (TorsN A l)] :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l) := by sorry
