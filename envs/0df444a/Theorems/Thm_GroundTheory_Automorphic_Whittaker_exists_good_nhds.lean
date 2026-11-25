-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_good_nhds
-- name    : GroundTheory.Automorphic.Whittaker.exists_good_nhds
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:15.705571+00:00
-- url     : https://prove2.me/theorems/cd7c3d13-b6c6-404a-93c1-1344a10f5787
-- title:
--   Whittaker: exists good nhds
-- statement:
--   The Whittaker construction uses the exists good nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L573-L682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L573-L682

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

theorem GroundTheory.Automorphic.Whittaker.exists_good_nhds (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) (x : GL (Fin n) F) :
    ∃ V : Set (GL (Fin n) F), IsOpen V ∧ x ∈ V ∧ supportedIn V ≤ goodSub n ψ₀ := by sorry
