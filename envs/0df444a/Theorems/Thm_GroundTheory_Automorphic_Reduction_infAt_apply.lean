-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
-- name    : GroundTheory.Automorphic.Reduction.infAt_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:37.287061+00:00
-- url     : https://prove2.me/theorems/44415048-37e3-480a-b5ce-49d72e2a0fa7
-- title:
--   Reduction: inf At apply
-- statement:
--   The Reduction construction uses the inf At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L64-L65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.infAt_apply (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    infAt w g a b = (g a b).1 w := by sorry

attribute [defeq] GroundTheory.Automorphic.Reduction.infAt_apply
