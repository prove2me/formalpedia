-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_units
-- name    : GroundTheory.ProfCoh.AdditiveFunction.g_units
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:52:53.77623+00:00
-- url     : https://prove2.me/theorems/064f68a8-c8e1-4c6c-8a4d-237e9e4e5c44
-- title:
--   Additive Function: g units
-- statement:
--   The Additive Function construction uses the g units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L252-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L252-L270

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

theorem GroundTheory.ProfCoh.AdditiveFunction.g_units :
    letI := repAction (unitsRep K L)
    d.g (Additive (𝓞 L)ˣ) =
      d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) -
        d.one := by sorry
