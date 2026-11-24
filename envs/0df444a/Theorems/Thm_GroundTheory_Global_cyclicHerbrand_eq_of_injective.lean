-- Prove2me | Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_of_injective
-- name    : GroundTheory.Global.cyclicHerbrand_eq_of_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:50.755827+00:00
-- url     : https://prove2.me/theorems/47b12684-c5d3-418b-b4ff-5b18a50578a9
-- title:
--   Global: cyclic Herbrand eq of injective
-- statement:
--   The Global construction uses the cyclic Herbrand eq of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L26-L34

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

theorem GroundTheory.Global.cyclicHerbrand_eq_of_injective [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ)
    [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by sorry
