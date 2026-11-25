-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem
-- name    : GroundTheory.Automorphic.Reduction.norm_le_one_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:17.738157+00:00
-- url     : https://prove2.me/theorems/e83145e9-51e7-4062-9df3-15e8814e5e5d
-- title:
--   Reduction: norm le one of mem
-- statement:
--   The Reduction construction uses the norm le one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L155-L158

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
variable (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Automorphic.Reduction.norm_le_one_of_mem {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 := by sorry
