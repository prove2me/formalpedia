-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_eq_of_torsion_trivial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:20.710074+00:00
-- url     : https://prove2.me/theorems/ae589bbf-e3d0-455e-ba20-0409e7d84860
-- title:
--   Additive Function: g eq of torsion trivial
-- statement:
--   The Additive Function construction uses the g eq of torsion trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L37-L42

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

theorem GroundTheory.ProfCoh.AdditiveFunction.g_eq_of_torsion_trivial (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    [Finite (ModN A l)] (hA : ∀ a : A, l • a = 0 → a = 0) :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) := by sorry
