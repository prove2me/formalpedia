-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_sUnits
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_sUnits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:00.326886+00:00
-- url     : https://prove2.me/theorems/f89072e2-cd72-59fd-ad30-c1e16ead0790
-- title:
--   Additive Function: g s Units
-- statement:
--   The Additive Function construction uses the g s Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L272-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L272-L295

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
variable {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (L ≃ₐ[K] L))

theorem GroundTheory.ProfCoh.AdditiveFunction.g_sUnits (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
    (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := sUnitAction S hS
    letI := stableMulAction S hS
    d.g (Additive (S.unit L)) =
      d.toFun (S → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) S) +
        d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) -
          d.one := by sorry
