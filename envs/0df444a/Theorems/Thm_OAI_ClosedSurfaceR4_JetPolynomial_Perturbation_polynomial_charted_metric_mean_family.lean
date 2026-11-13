-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_metric_mean_family
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:51.8842+00:00
-- url     : https://prove2.me/theorems/79333b22-fb64-49fc-aeb3-273225e8cdcb
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialChartedMeanFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialChartedMeanFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation`, with `open Set TopologicalSpace`, `open scoped ContDiff NNReal BigOperators`, `open PhaseMean RealModes RootMean WeightedEstimates FiniteMean`):
--
--   ```lean
--   theorem polynomial_charted_metric_mean_family (q : ℕ) :
--       ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
--       ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
--         {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
--         {K : ι → Compacts Base} {s : ℝ≥0}
--         (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
--         {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
--         (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
--         ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) → (∀ m, (Fintype.card ι : ℝ) ≤ J m) →
--         (∀ i m, ρ⁻¹ ≤ J m ∧ (d i).budgets.inv (m+q+2) ≤ J m ∧
--           (d i).budgets.forms (m+q+2) ≤ J m ∧ (d i).budgets.psi (m+q+2) ≤ J m ∧
--           (d i).budgets.mode (m+q+2) ≤ J m ∧ (d i).budgets.normal (m+q+2) ≤ J m ∧
--           (d i).budgets.chi m ≤ J m ∧ (d i).budgets.pull m ≤ J m) →
--         ∀ δ : ℝ, 0 < δ →
--         MeanBounds univ s reference r (q+2)
--           (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
--           (polynomialMeanProfile p C J) (polynomialMeanProfile p C J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.MeanBounds`, `OAI.ClosedSurfaceR4.FiniteMean.rescaledMean`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PhaseMean.polynomialMeanProfile` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.chartedFamilyMean` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialChartedMeanFamily.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_charted_metric_mean_family)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

theorem polynomial_charted_metric_mean_family (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {s : ℝ≥0}
      (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) → (∀ m, (Fintype.card ι : ℝ) ≤ J m) →
      (∀ i m, ρ⁻¹ ≤ J m ∧ (d i).budgets.inv (m+q+2) ≤ J m ∧
        (d i).budgets.forms (m+q+2) ≤ J m ∧ (d i).budgets.psi (m+q+2) ≤ J m ∧
        (d i).budgets.mode (m+q+2) ≤ J m ∧ (d i).budgets.normal (m+q+2) ≤ J m ∧
        (d i).budgets.chi m ≤ J m ∧ (d i).budgets.pull m ≤ J m) →
      ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s reference r (q+2)
        (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
        (polynomialMeanProfile p C J) (polynomialMeanProfile p C J) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
