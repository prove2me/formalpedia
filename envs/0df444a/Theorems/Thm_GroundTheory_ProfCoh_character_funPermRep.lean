-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_character_funPermRep
-- name    : GroundTheory.ProfCoh.character_funPermRep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:51.502995+00:00
-- url     : https://prove2.me/theorems/b90390df-dde0-49e9-902c-fc10902cefa3
-- title:
--   Prof Coh: character fun Perm Rep
-- statement:
--   The Prof Coh construction uses the character fun Perm Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L20-L31

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

theorem GroundTheory.ProfCoh.character_funPermRep (X : Type*) [MulAction Γ X] [Finite X] (γ : Γ) :
    (funPermRep k Γ X).character γ = Nat.card (MulAction.fixedBy X γ) := by sorry
