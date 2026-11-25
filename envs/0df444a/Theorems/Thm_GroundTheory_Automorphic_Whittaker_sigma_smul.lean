-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_smul
-- name    : GroundTheory.Automorphic.Whittaker.sigma_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:36:04.766652+00:00
-- url     : https://prove2.me/theorems/25b5fc49-38fb-4e23-9fa8-a063bf03bba4
-- title:
--   Whittaker: sigma smul
-- statement:
--   The Whittaker construction uses the sigma smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L74-L76

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
variable (ψ₀ : AddChar F ℂ)
omit ψ₀

theorem GroundTheory.Automorphic.Whittaker.sigma_smul (h : NN F n) (g : GL (Fin n) F) : sigma (h • g) = swapTheta h • sigma g := by sorry
