-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_indicator
-- name    : GroundTheory.Automorphic.Whittaker.transl_indicator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:19.861912+00:00
-- url     : https://prove2.me/theorems/b0034440-adf3-5dec-b3b3-711438e1939d
-- title:
--   Whittaker: transl indicator
-- statement:
--   The Whittaker construction uses the transl indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L41-L48

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

theorem GroundTheory.Automorphic.Whittaker.transl_indicator (h : H) (A : Set X) : transl h (A.indicator 1) = (h • A).indicator 1 := by sorry
