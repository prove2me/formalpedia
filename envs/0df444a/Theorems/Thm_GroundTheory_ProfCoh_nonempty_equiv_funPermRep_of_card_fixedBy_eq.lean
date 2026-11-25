-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_nonempty_equiv_funPermRep_of_card_fixedBy_eq
-- name    : GroundTheory.ProfCoh.nonempty_equiv_funPermRep_of_card_fixedBy_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:03.0062+00:00
-- url     : https://prove2.me/theorems/34689687-b524-4589-81ec-35b303250e93
-- title:
--   Prof Coh: nonempty equiv fun Perm Rep of card fixed By eq
-- statement:
--   The Prof Coh construction uses the nonempty equiv fun Perm Rep of card fixed By eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L33-L41

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
variable {k : Type*} {Γ : Type*} [Field k] [Group Γ]

theorem GroundTheory.ProfCoh.nonempty_equiv_funPermRep_of_card_fixedBy_eq [CharZero k] [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    Nonempty ((funPermRep k Γ X).Equiv (funPermRep k Γ X')) := by sorry
