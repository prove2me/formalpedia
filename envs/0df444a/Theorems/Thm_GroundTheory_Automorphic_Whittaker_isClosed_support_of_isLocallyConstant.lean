-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isClosed_support_of_isLocallyConstant
-- name    : GroundTheory.Automorphic.Whittaker.isClosed_support_of_isLocallyConstant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:41.953489+00:00
-- url     : https://prove2.me/theorems/a63ae428-a82d-49b6-a7b8-b7c3294b0481
-- title:
--   Whittaker: is Closed support of is Locally Constant
-- statement:
--   The Whittaker construction uses the is Closed support of is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L42-L48

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
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
open Set Topology
variable {X : Type*} [TopologicalSpace X]

theorem GroundTheory.Automorphic.Whittaker.isClosed_support_of_isLocallyConstant {f : X → ℂ} (hf : IsLocallyConstant f) :
    IsClosed (Function.support f) := by sorry
