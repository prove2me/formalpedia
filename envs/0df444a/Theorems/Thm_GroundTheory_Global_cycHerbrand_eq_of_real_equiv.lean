-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_real_equiv
-- name    : GroundTheory.Global.cycHerbrand_eq_of_real_equiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:32.42573+00:00
-- url     : https://prove2.me/theorems/50c7ac5f-55df-49b7-a959-9ffc57ceec50
-- title:
--   Global: cyc Herbrand eq of real equiv
-- statement:
--   The Global construction uses the cyc Herbrand eq of real equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/LatticeBridge.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/LatticeBridge.lean#L22-L28

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
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
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.Global.cycHerbrand_eq_of_real_equiv {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M']
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ := by sorry
