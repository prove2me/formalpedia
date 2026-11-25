-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_logLatticeProd_real_equiv
-- name    : GroundTheory.ProfCoh.exists_logLatticeProd_real_equiv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:25.764802+00:00
-- url     : https://prove2.me/theorems/264650ce-db13-4bdd-85f0-3c0334b8e71f
-- title:
--   Prof Coh: exists log Lattice Prod real equiv
-- statement:
--   The Prof Coh construction uses the exists log Lattice Prod real equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L133-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L133-L185

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

theorem GroundTheory.ProfCoh.exists_logLatticeProd_real_equiv :
    ∃ e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ),
      ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep K L).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
        (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by sorry
