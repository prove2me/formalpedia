-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_swapTheta_mem_prod
-- name    : GroundTheory.Automorphic.Whittaker.swapTheta_mem_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:43.116745+00:00
-- url     : https://prove2.me/theorems/7884a625-5180-4481-96ad-32943d34bf5d
-- title:
--   Whittaker: swap Theta mem prod
-- statement:
--   The Whittaker construction uses the swap Theta mem prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L426-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L426-L436

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
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.swapTheta_mem_prod {K : Subgroup (Iwasawa.unipotent F n)} {l : NN F n}
    (hl : l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K) :
    swapTheta l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K := by sorry
