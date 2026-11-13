-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_seed_bound
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:58.056213+00:00
-- url     : https://prove2.me/theorems/8d68300f-dd2d-43bf-96ed-9cfb82644d4f
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/ChartedUniformSeed.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/ChartedUniformSeed.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation`, with `open TopologicalSpace`, `open scoped ContDiff NNReal`, `open PhaseMean RealModes WeightedEstimates FiniteMean`):
--
--   ```lean
--   theorem uniform_charted_seed_bound {n : ℕ} {P : Fin 3 → Fin n → Expression}
--       (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
--       ∃ B : ℝ, 1 ≤ B ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
--         {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
--         {c : PolynomialSolveData P ε G hG φ K τ s}
--         {r : ℝ} {reference : SmallModes.Base → Tensor}
--         (d : ChartedMeanData c r ρ R reference), p.Fits d →
--         0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
--         τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
--         ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
--         WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
--         WeightedBound Set.univ s m (B * (δ * τ)) (d.freeAmplitude hρ δ q A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.inputOrder` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile.Fits` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData.freeAmplitude` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/ChartedUniformSeed.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_charted_seed_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_seed_bound {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ s m (B * (δ * τ)) (d.freeAmplitude hρ δ q A) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
