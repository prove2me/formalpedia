-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_isIrreducible_comp
-- name    : GroundTheory.Automorphic.ContragredientTranspose.isIrreducible_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:26.79032+00:00
-- url     : https://prove2.me/theorems/2684d565-5fd3-5cc8-a0ec-63065276d4e6
-- title:
--   Contragredient Transpose: is Irreducible comp
-- statement:
--   The Contragredient Transpose construction uses the is Irreducible comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.isIrreducible_comp {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (α : G ≃* G) :
    Representation.IsIrreducible (ρ.comp α.toMonoidHom) := by sorry
