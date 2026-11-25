-- Prove2me | Theorems.Thm_GlobalTheory_T_topologicalClosure_stable_linearForm_mul_and_fourier
-- name    : GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:43.783076+00:00
-- url     : https://prove2.me/theorems/ff3f7b25-a19a-56d2-8c7e-a161d76055ea
-- title:
--   T: topological Closure stable linear Form mul and fourier
-- statement:
--   The T construction uses the topological Closure stable linear Form mul and fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzClosureStableLinearFormFourierStatement.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzClosureStableLinearFormFourierStatement.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourier
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourierStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by sorry
