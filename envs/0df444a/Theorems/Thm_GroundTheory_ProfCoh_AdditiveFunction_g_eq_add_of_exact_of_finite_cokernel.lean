-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_add_of_exact_of_finite_cokernel
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_eq_add_of_exact_of_finite_cokernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:05.382233+00:00
-- url     : https://prove2.me/theorems/dac8f511-4747-40c9-92e4-7ed2c19af7df
-- title:
--   Additive Function: g eq add of exact of finite cokernel
-- statement:
--   The Additive Function construction uses the g eq add of exact of finite cokernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L46-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L46-L70

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c

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
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} [NeZero l] {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem GroundTheory.ProfCoh.AdditiveFunction.g_eq_add_of_exact_of_finite_cokernel {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C] (f : A →+ B) (p : B →+ C)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b)
    (hf : Function.Injective f) (hfp : Function.Exact f p) [Finite (C ⧸ p.range)] :
    d.g B = d.g A + d.g C := by sorry
