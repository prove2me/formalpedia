-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_logLatticeProd_intertwiner
-- name    : GroundTheory.ProfCoh.exists_logLatticeProd_intertwiner
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:51:52.416626+00:00
-- url     : https://prove2.me/theorems/3c99aca6-6133-5c52-98f6-afd5a4d521ad
-- title:
--   Prof Coh: exists log Lattice Prod intertwiner
-- statement:
--   The Prof Coh construction uses the exists log Lattice Prod intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L187-L194

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
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
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.ProfCoh.exists_logLatticeProd_intertwiner :
    ∃ φ : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ (g : L ≃ₐ[K] L) x, φ (((logLatticeRep K L).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
        funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g (φ x) := by sorry
