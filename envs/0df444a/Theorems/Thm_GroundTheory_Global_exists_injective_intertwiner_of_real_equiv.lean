-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_injective_intertwiner_of_real_equiv
-- name    : GroundTheory.Global.exists_injective_intertwiner_of_real_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:43:19.246383+00:00
-- url     : https://prove2.me/theorems/d7d7ce30-8b3a-4f1f-9fb9-7256ca69783b
-- title:
--   Global: exists injective intertwiner of real equiv
-- statement:
--   The Global construction uses the exists injective intertwiner of real equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L118-L129

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

theorem GroundTheory.Global.exists_injective_intertwiner_of_real_equiv (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by sorry
