-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_piScalarRight_baseChange_funPermRep
-- name    : GroundTheory.ProfCoh.piScalarRight_baseChange_funPermRep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:32.45921+00:00
-- url     : https://prove2.me/theorems/c6cd425a-bf19-44e7-aad9-2801c57cb30c
-- title:
--   Prof Coh: pi Scalar Right base Change fun Perm Rep
-- statement:
--   The Prof Coh construction uses the pi Scalar Right base Change fun Perm Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLattice.lean#L49-L58

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

theorem GroundTheory.ProfCoh.piScalarRight_baseChange_funPermRep (X : Type*) [MulAction Γ X] [Fintype X]
    [DecidableEq X] (γ : Γ) (x : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      funPermRep ℝ Γ X γ (TensorProduct.piScalarRight ℤ ℝ ℝ X x) := by sorry
