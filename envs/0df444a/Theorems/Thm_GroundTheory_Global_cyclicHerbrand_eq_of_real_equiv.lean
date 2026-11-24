-- Prove2me | Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_of_real_equiv
-- name    : GroundTheory.Global.cyclicHerbrand_eq_of_real_equiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:40.72836+00:00
-- url     : https://prove2.me/theorems/5504f95e-46ae-4809-80bf-ca65c15567cf
-- title:
--   Global: cyclic Herbrand eq of real equiv
-- statement:
--   The Global construction uses the cyclic Herbrand eq of real equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L131-L140

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
open scoped TensorProduct
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']

theorem GroundTheory.Global.cyclicHerbrand_eq_of_real_equiv [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by sorry
