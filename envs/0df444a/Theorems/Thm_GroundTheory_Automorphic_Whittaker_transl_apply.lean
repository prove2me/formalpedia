-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- name    : GroundTheory.Automorphic.Whittaker.transl_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:37.460043+00:00
-- url     : https://prove2.me/theorems/f131d53a-01db-4031-b550-c4cb5c9cddad
-- title:
--   Whittaker: transl apply
-- statement:
--   The Whittaker construction uses the transl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L20-L20

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

theorem GroundTheory.Automorphic.Whittaker.transl_apply (h : H) (f : X → ℂ) (x : X) : transl h f x = f (h⁻¹ • x) := by sorry

attribute [defeq] GroundTheory.Automorphic.Whittaker.transl_apply
