-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_sign_traceGram
-- name    : GroundTheory.Automorphic.exists_sign_traceGram
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:07.399225+00:00
-- url     : https://prove2.me/theorems/ea013d69-af07-469e-be34-9bb682231114
-- title:
--   Automorphic: exists sign trace Gram
-- statement:
--   The Automorphic construction uses the exists sign trace Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L117-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L117-L160

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
omit [NumberField K]

theorem GroundTheory.Automorphic.exists_sign_traceGram {w : InfinitePlace K} (hw : w.IsReal)
    (hdef : IsHermDefiniteAt H w hw) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ v : ι × κ → ℝ, v ≠ 0 →
      0 < ε * ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by sorry
