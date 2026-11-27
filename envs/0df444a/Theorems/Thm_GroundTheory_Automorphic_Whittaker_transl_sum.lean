-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_sum
-- name    : GroundTheory.Automorphic.Whittaker.transl_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:48.778261+00:00
-- url     : https://prove2.me/theorems/095915bc-6b1b-4c2c-85aa-17e139080947
-- title:
--   Whittaker: transl sum
-- statement:
--   The Whittaker construction uses the transl sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L36-L39

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

theorem GroundTheory.Automorphic.Whittaker.transl_sum {ι : Type*} (h : H) (s : Finset ι) (f : ι → X → ℂ) :
    transl h (∑ i ∈ s, f i) = ∑ i ∈ s, transl h (f i) := by sorry
