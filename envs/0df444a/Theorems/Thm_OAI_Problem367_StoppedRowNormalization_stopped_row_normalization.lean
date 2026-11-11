-- Prove2me | Theorems.Thm_OAI_Problem367_StoppedRowNormalization_stopped_row_normalization
-- name    : OAI.Problem367.StoppedRowNormalization.stopped_row_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:55.215721+00:00
-- url     : https://prove2.me/theorems/b0d044dd-3fd2-49ce-a1df-f6353abbc0ec
-- title:
--   OAI.Problem367.StoppedRowNormalization.stopped_row_normalization: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.StoppedRowNormalization.stopped_row_normalization` of [lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.StoppedRowNormalization`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open BrownianGrid BrownianIntegralProcess`):
--
--   ```lean
--   theorem stopped_row_normalization {ι : Type*} [IsProbabilityMeasure P]
--       {F : Filtration ℝ≥0 mΩ} {B C R I J : ι → ℝ≥0 → Ω → ℝ}
--       {M Z K : ℝ≥0 → Ω → ℝ}
--       (hB : ∀ a, IsPreBrownianReal (B a) P)
--       (hAd : ∀ a, StronglyAdapted F (B a))
--       (hind : ∀ a s t, s ≤ t → Indep
--         (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P)
--       (hcB : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
--       (hC : ∀ a, StronglyAdapted F (C a)) (hR : ∀ a, StronglyAdapted F (R a))
--       (hK : StronglyAdapted F K)
--       (hcC : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => C a t ω))
--       (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
--       {c r : ι → ℝ} {k : ℝ} (hc : ∀ a, 0 ≤ c a) (hk : 0 ≤ k)
--       (hbC : ∀ a, ∀ᵐ ω ∂P, ∀ t, |C a t ω| ≤ c a)
--       (hbR : ∀ a, ∀ᵐ ω ∂P, ∀ t, |R a t ω| ≤ r a)
--       (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ k)
--       (hI : ∀ a, Martingale (I a) F P) (hJ : ∀ a, Martingale (J a) F P)
--       (hM : Martingale M F P) (hZ : Martingale Z F P)
--       (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
--       (hM2 : ∀ t, MemLp (M t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
--       (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
--       (hcJ : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => J a t ω))
--       (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
--       (hcZ : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
--       (hpI : ∀ a, IsStronglyProgressive F (I a)) (hpM : IsStronglyProgressive F M)
--       (T : ℝ≥0)
--       (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)))
--       (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
--       (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
--         (uniformSum (B a) (C a) T n ω - I a T ω) ^ 2 ∂P) atTop (𝓝 0))
--       (hJlim : ∀ a, Tendsto (fun n => ∫ ω,
--         (uniformSum (B a) (R a) T n ω - J a T ω) ^ 2 ∂P) atTop (𝓝 0))
--       {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
--       (hlocal : ∀ a, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
--         K t ω * C a t ω = R a t ω) :
--       Tendsto (fun n => ∫ ω,
--         (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess Z τ T ω) ^ 2 ∂P)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Martingales/StoppedRowNormalization.lean (declaration OAI.Problem367.StoppedRowNormalization.stopped_row_normalization)

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

theorem stopped_row_normalization {ι : Type*} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B C R I J : ι → ℝ≥0 → Ω → ℝ}
    {M Z K : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ a s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcB : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hC : ∀ a, StronglyAdapted F (C a)) (hR : ∀ a, StronglyAdapted F (R a))
    (hK : StronglyAdapted F K)
    (hcC : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => C a t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {c r : ι → ℝ} {k : ℝ} (hc : ∀ a, 0 ≤ c a) (hk : 0 ≤ k)
    (hbC : ∀ a, ∀ᵐ ω ∂P, ∀ t, |C a t ω| ≤ c a)
    (hbR : ∀ a, ∀ᵐ ω ∂P, ∀ t, |R a t ω| ≤ r a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ k)
    (hI : ∀ a, Martingale (I a) F P) (hJ : ∀ a, Martingale (J a) F P)
    (hM : Martingale M F P) (hZ : Martingale Z F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcJ : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => J a t ω))
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hcZ : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hpI : ∀ a, IsStronglyProgressive F (I a)) (hpM : IsStronglyProgressive F M)
    (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (C a) T n ω - I a T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (R a) T n ω - J a T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ a, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C a t ω = R a t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess Z τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  sorry

end Problem367.StoppedRowNormalization

end

end OAI
end
