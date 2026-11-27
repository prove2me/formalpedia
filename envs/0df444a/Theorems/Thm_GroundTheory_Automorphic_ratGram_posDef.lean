-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ratGram_posDef
-- name    : GroundTheory.Automorphic.ratGram_posDef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:07.555703+00:00
-- url     : https://prove2.me/theorems/b5419f24-2b53-4d46-b360-f4585ad9ce9f
-- title:
--   Automorphic: rat Gram pos Def
-- statement:
--   The Automorphic construction uses the rat Gram pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L267-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L267-L320

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

theorem GroundTheory.Automorphic.ratGram_posDef (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    (v : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by sorry
