-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mul
-- name    : GroundTheory.Automorphic.Whittaker.transl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:44.462048+00:00
-- url     : https://prove2.me/theorems/1ece03b7-1fae-4ef6-99a6-ad5b7b08678c
-- title:
--   Whittaker: transl mul
-- statement:
--   The Whittaker construction uses the transl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L22-L24

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

theorem GroundTheory.Automorphic.Whittaker.transl_mul (h k : H) (f : X → ℂ) : transl (h * k) f = transl h (transl k f) := by sorry
