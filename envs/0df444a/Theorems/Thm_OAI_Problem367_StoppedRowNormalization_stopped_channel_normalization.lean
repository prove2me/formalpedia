-- Prove2me | Theorems.Thm_OAI_Problem367_StoppedRowNormalization_stopped_channel_normalization
-- name    : OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:29.576704+00:00
-- url     : https://prove2.me/theorems/33dfcc5a-b1cd-4c01-b1cb-4d54a213201f
-- title:
--   OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization` of [lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.StoppedRowNormalization`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open BrownianGrid BrownianIntegralProcess`):
--
--   ```lean
--   theorem stopped_channel_normalization
--       {F : Filtration ℝ≥0 mΩ} {B C R K I J : ℝ≥0 → Ω → ℝ}
--       (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
--       (hind : ∀ s t, s ≤ t → Indep
--         (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
--       (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
--       (hC : StronglyAdapted F C) (hR : StronglyAdapted F R) (hK : StronglyAdapted F K)
--       (hcC : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
--       (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
--       {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
--       (hbC : ∀ᵐ ω ∂P, ∀ t, |C t ω| ≤ a)
--       (hbR : ∀ᵐ ω ∂P, ∀ t, |R t ω| ≤ b)
--       (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ c)
--       (hI : Martingale I F P) (hJ : Martingale J F P)
--       (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
--       (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
--       (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
--       (T : ℝ≥0)
--       (hIlim : Tendsto (fun n => ∫ ω,
--         (uniformSum B C T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
--       (hJlim : Tendsto (fun n => ∫ ω,
--         (uniformSum B R T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
--       {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
--       (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
--         K t ω * C t ω = R t ω) :
--       Tendsto (fun n => ∫ ω,
--         (uniformSum (stoppedProcess I τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.StoppedRowNormalization.stopped_row_normalization` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean (declaration OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_Q243FI001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedRowNormalization
open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_channel_normalization
    {F : Filtration ℝ≥0 mΩ} {B C R K I J : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hC : StronglyAdapted F C) (hR : StronglyAdapted F R) (hK : StronglyAdapted F K)
    (hcC : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbC : ∀ᵐ ω ∂P, ∀ t, |C t ω| ≤ a)
    (hbR : ∀ᵐ ω ∂P, ∀ t, |R t ω| ≤ b)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ c)
    (hI : Martingale I F P) (hJ : Martingale J F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (uniformSum B C T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (uniformSum B R T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C t ω = R t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess I τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  sorry

end Problem367.StoppedRowNormalization

end

end OAI
end
