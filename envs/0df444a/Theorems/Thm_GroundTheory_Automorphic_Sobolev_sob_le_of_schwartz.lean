-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_le_of_schwartz
-- name    : GroundTheory.Automorphic.Sobolev.sob_le_of_schwartz
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:28.939812+00:00
-- url     : https://prove2.me/theorems/29deeb3b-44fd-48a5-bca7-a1efb5c4588b
-- title:
--   Sobolev: sob le of schwartz
-- statement:
--   The Sobolev construction uses the sob le of schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L441-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L441-L500

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.sob_le_of_schwartz (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) {s t C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(E, ℂ), sob t (T φ) ≤ ENNReal.ofReal C * sob s (φ : 𝓢'(E, ℂ))) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) : sob t (T u) ≤ ENNReal.ofReal C * sob s u := by sorry
