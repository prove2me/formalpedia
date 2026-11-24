-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_sub
-- name    : GroundTheory.Automorphic.Whittaker.transl_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:48.579456+00:00
-- url     : https://prove2.me/theorems/e56cf05e-0ded-417c-b6a4-a4253fbc7fb4
-- title:
--   Whittaker: transl sub
-- statement:
--   The Whittaker construction uses the transl sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L32-L32

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

theorem GroundTheory.Automorphic.Whittaker.transl_sub (h : H) (f g : X → ℂ) : transl h (f - g) = transl h f - transl h g := by sorry
