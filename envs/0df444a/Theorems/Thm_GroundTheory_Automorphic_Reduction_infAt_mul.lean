-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_mul
-- name    : GroundTheory.Automorphic.Reduction.infAt_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:41.866318+00:00
-- url     : https://prove2.me/theorems/53e77947-ec9a-45e4-ab44-701e5e6440e3
-- title:
--   Reduction: inf At mul
-- statement:
--   The Reduction construction uses the inf At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L70-L72

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

theorem GroundTheory.Automorphic.Reduction.infAt_mul (w : InfinitePlace K) (g h : AdelicGLn.AdelicGL K n) :
    infAt w (g * h) = infAt w g * infAt w h := by sorry
