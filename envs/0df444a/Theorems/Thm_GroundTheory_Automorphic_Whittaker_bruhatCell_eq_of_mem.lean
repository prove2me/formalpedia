-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_of_mem
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_eq_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:35.376545+00:00
-- url     : https://prove2.me/theorems/804dc31c-17d9-4f99-bef0-4d72c840ebeb
-- title:
--   Whittaker: bruhat Cell eq of mem
-- statement:
--   The Whittaker construction uses the bruhat Cell eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L179-L181

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_eq_of_mem {g h : GL (Fin n) F} (h₁ : h ∈ cellGe g) (h₂ : h ∈ cellLe g) :
    bruhatCell h = bruhatCell g := by sorry
