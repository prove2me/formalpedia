-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaProcessStrictIncreaseAndInfiniteActivity
-- name    : Kyprianou.Ch01.gammaProcessStrictIncreaseAndInfiniteActivity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:10:45.792651+00:00
-- url     : https://prove2.me/theorems/e500fa3a-3f05-4047-be27-b24540358458
-- title:
--   §1.2.4: gamma process strictly increasing paths and infinite-activity Lévy measure
-- statement:
--   Kyprianou (2006) §1.2.4, printed p. 8. A gamma Lévy process with rate alpha>0, shape rate beta>0, and Laplace transform E exp(−q X_t)=(alpha/(alpha+q))^(beta t) has almost surely strictly increasing sample paths; its Lévy measure Π(dx)=beta e^(−alpha x)/x dx is a legitimate Lévy measure and has infinite total mass on positive jumps. The transform and Lévy-process structure are independent inputs; strict sample-path increase and infinite jump intensity are substantive conclusions. This captures the book's distinction between a gamma process and a positive-jump compound Poisson process.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4, printed pp. 7–8, gamma process paragraph after Lemma 1.7.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaProcessStrictIncreaseAndInfiniteActivity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (hAlpha : 0 < alpha) (hBeta : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hGammaLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    (∀ᵐ ω ∂P, StrictMono (fun t : ℝ≥0 => X t ω)) ∧
      IsLevyMeasure (Kyprianou.Ch01.gammaLevyMeasure alpha beta) ∧
      (Kyprianou.Ch01.gammaLevyMeasure alpha beta)
        (Set.Ioi (0 : ℝ)) = (⊤ : ℝ≥0∞) := by
  sorry
