-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_hasFDerivAt_of_norming
-- name    : GlobalTheory.RealWeil.hasFDerivAt_of_norming
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:32.4418+00:00
-- url     : https://prove2.me/theorems/68aed3de-8c24-4f8a-9e00-3ab7d810cfaf
-- title:
--   Real Weil: has FDeriv At of norming
-- statement:
--   The Real Weil construction uses the has FDeriv At of norming property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSet.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergSmoothOfWeakDerivativeClosedSet.lean#L9-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by sorry
