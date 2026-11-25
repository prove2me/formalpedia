-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_biAction_smul
-- name    : GroundTheory.Automorphic.Whittaker.biAction_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:10.035803+00:00
-- url     : https://prove2.me/theorems/17d31a47-fb1a-4e5d-bd1c-2dd030fb3fb1
-- title:
--   Whittaker: bi Action smul
-- statement:
--   The Whittaker construction uses the bi Action smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L39-L40

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

theorem GroundTheory.Automorphic.Whittaker.biAction_smul (h : NN F n) (g : GL (Fin n) F) :
    h • g = (h.1 : GL (Fin n) F) * g * (h.2 : GL (Fin n) F)⁻¹ := by sorry
