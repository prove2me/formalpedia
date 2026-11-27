-- Prove2me | Theorems.Thm_GlobalTheory_MultilinFubini_integral_vecOn
-- name    : GlobalTheory.MultilinFubini.integral_vecOn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:03:07.114574+00:00
-- url     : https://prove2.me/theorems/2129ec18-121b-5ee4-94e7-50ac727e0ae2
-- title:
--   Multilin Fubini: integral vec On
-- statement:
--   The Multilin Fubini construction uses the integral vec On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralContinuousMultilinearMapPiMeasure.lean#L58-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralContinuousMultilinearMapPiMeasure.lean#L58-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.MultilinFubini
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem GlobalTheory.MultilinFubini.integral_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by sorry
