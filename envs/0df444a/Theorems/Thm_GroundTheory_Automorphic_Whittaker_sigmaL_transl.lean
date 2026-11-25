-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_transl
-- name    : GroundTheory.Automorphic.Whittaker.sigmaL_transl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:27.286709+00:00
-- url     : https://prove2.me/theorems/ec3fd356-1096-4399-ba3b-ee78bfbdd3c7
-- title:
--   Whittaker: sigma L transl
-- statement:
--   The Whittaker construction uses the sigma L transl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L99-L104

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
variable [TopologicalSpace F] [IsTopologicalRing F]

theorem GroundTheory.Automorphic.Whittaker.sigmaL_transl (h : NN F n) (f : GL (Fin n) F → ℂ) :
    sigmaL (transl h f) = transl (swapTheta h) (sigmaL f) := by sorry
