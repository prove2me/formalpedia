-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_zero_of_nsmul_eq_zero
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_eq_zero_of_nsmul_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:07.947576+00:00
-- url     : https://prove2.me/theorems/0ed6add1-6425-44e3-b2ab-433301a0386e
-- title:
--   Additive Function: g eq zero of nsmul eq zero
-- statement:
--   The Additive Function construction uses the g eq zero of nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean#L44-L63

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

theorem GroundTheory.ProfCoh.AdditiveFunction.g_eq_zero_of_nsmul_eq_zero (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (hA : ∀ a : A, l • a = 0) : d.g A = 0 := by sorry
