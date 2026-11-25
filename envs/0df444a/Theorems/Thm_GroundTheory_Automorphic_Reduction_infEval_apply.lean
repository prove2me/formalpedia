-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
-- name    : GroundTheory.Automorphic.Reduction.infEval_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:10.029638+00:00
-- url     : https://prove2.me/theorems/d1450eb4-b6f5-4f4a-9cfd-4479a2fbdc77
-- title:
--   Reduction: inf Eval apply
-- statement:
--   The Reduction construction uses the inf Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L84-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L84-L84

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

theorem GroundTheory.Automorphic.Reduction.infEval_apply (w : InfinitePlace K) (a : 𝔸[K]) : infEval w a = a.1 w := by sorry

attribute [defeq] GroundTheory.Automorphic.Reduction.infEval_apply
