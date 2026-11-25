-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_le_of_integral
-- name    : GroundTheory.Automorphic.Reduction.norm_vecMul_le_of_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:25.230104+00:00
-- url     : https://prove2.me/theorems/2443c176-c284-4dc1-b25f-1acffa657f16
-- title:
--   Reduction: norm vec Mul le of integral
-- statement:
--   The Reduction construction uses the norm vec Mul le of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L160-L169

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

theorem GroundTheory.Automorphic.Reduction.norm_vecMul_le_of_integral {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers K) (z : Fin n → v.adicCompletion K) :
    ‖z ᵥ* M‖ ≤ ‖z‖ := by sorry
