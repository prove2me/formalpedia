-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_smul
-- name    : GroundTheory.Automorphic.Whittaker.transl_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:22.790155+00:00
-- url     : https://prove2.me/theorems/6cf456b5-c604-4809-96cb-c953d79f54b0
-- title:
--   Whittaker: transl smul
-- statement:
--   The Whittaker construction uses the transl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L34-L34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
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
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} {H : Type*} [Group H] [MulAction H X]

theorem GroundTheory.Automorphic.Whittaker.transl_smul (h : H) (c : ℂ) (f : X → ℂ) : transl h (c • f) = c • transl h f := by sorry
