-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply_biAction
-- name    : GroundTheory.Automorphic.Whittaker.transl_apply_biAction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:54.506985+00:00
-- url     : https://prove2.me/theorems/bd373fe9-e304-4c8c-aebd-7a4150d12825
-- title:
--   Whittaker: transl apply bi Action
-- statement:
--   The Whittaker construction uses the transl apply bi Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L42-L44

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

theorem GroundTheory.Automorphic.Whittaker.transl_apply_biAction (h : NN F n) (f : GL (Fin n) F → ℂ) (x : GL (Fin n) F) :
    transl h f x = f ((h.1 : GL (Fin n) F)⁻¹ * x * (h.2 : GL (Fin n) F)) := by sorry
