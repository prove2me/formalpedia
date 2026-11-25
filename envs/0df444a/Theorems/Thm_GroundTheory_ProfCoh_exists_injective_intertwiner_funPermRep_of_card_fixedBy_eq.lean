-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq
-- name    : GroundTheory.ProfCoh.exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:51.362365+00:00
-- url     : https://prove2.me/theorems/65b47099-150f-4260-98ca-3bb2ffe4fc61
-- title:
--   Prof Coh: exists injective intertwiner fun Perm Rep of card fixed By eq
-- statement:
--   The Prof Coh construction uses the exists injective intertwiner fun Perm Rep of card fixed By eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L60-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L60-L81

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLattice
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
open Module Representation GroundTheory.Global
open scoped TensorProduct
universe u v
variable {Γ : Type*} [Group Γ]

theorem GroundTheory.ProfCoh.exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x) := by sorry
