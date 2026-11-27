-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_ratVec
-- name    : GroundTheory.Automorphic.Reduction.infComp_ratVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:28.675289+00:00
-- url     : https://prove2.me/theorems/7d0c417b-33a7-4460-8285-8dca2ad26920
-- title:
--   Reduction: inf Comp rat Vec
-- statement:
--   The Reduction construction uses the inf Comp rat Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L193-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L193-L194

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

theorem GroundTheory.Automorphic.Reduction.infComp_ratVec (w : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    infComp w (ratVec x) i = (x i : w.Completion) := by sorry
