-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_annular_eigenfunction_separating_tensor
-- name    : OAI.YauCounterexamples.annular_eigenfunction_separating_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:32:51.815511+00:00
-- url     : https://prove2.me/theorems/298ff9d5-0cb0-4a83-8190-337c33488729
-- title:
--   OAI.YauCounterexamples.annular_eigenfunction_separating_tensor: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor` of [lean/OAI/Geometry/SmoothYau/Spectrum/AnnularOrthogonalTransverseNonzero.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/AnnularOrthogonalTransverseNonzero.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem annular_eigenfunction_separating_tensor [PreconnectedSpace (Sphere d)]
--       (μ : Measure (Sphere d)) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
--       (g : SmoothMetric (Euclidean d) (Sphere d))
--       (a b c : Euclidean (d+1))
--       (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
--       (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
--       (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
--       {u v : Sphere d → ℝ}
--       (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
--       (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
--       (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
--       (hve : ∀ p, -laplaceBeltrami g v p = ((n:ℝ)*((n:ℝ)+2))*v p)
--       (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
--         Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
--       (hgp : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
--         Complex.normSq (planarLinear a b p) < h →
--         ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean d) p),
--           g.inner p X Y = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
--             (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
--               (fun q : Sphere d => (q : Euclidean (d+1))) p X)
--             (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
--               (fun q : Sphere d => (q : Euclidean (d+1))) p Y))
--       (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) (hd : d = 3) :
--       ∃ χ : Sphere d → ℝ,
--         tsupport χ ⊆ {p | l < Complex.normSq (planarLinear a b p) ∧
--           Complex.normSq (planarLinear a b p) < h} ∧
--         ContMDiff 𝓘(ℝ,Euclidean d)
--           (𝓘(ℝ,Euclidean d).prod 𝓘(ℝ,Euclidean d →L[ℝ] Euclidean d)) ∞
--           (fun y => TotalSpace.mk' (Euclidean d →L[ℝ] Euclidean d) y
--             (supportedPinningTensor g u v χ y)) ∧
--         (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,Euclidean d) y)
--           (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
--         (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
--         0 < ∫ y, g.inner y (metricGradient g v y)
--           (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.metricGradient` and `OAI.YauCounterexamples.planarLinear` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.supportedPinningTensor` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_annular_simple_pinned_family` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/AnnularOrthogonalTransverseNonzero.lean (declaration OAI.YauCounterexamples.annular_eigenfunction_separating_tensor)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}

theorem annular_eigenfunction_separating_tensor [PreconnectedSpace (Sphere d)]
    (μ : Measure (Sphere d)) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    {u v : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hve : ∀ p, -laplaceBeltrami g v p = ((n:ℝ)*((n:ℝ)+2))*v p)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean d) p),
        g.inner p X Y = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p X)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p Y))
    (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) (hd : d = 3) :
    ∃ χ : Sphere d → ℝ,
      tsupport χ ⊆ {p | l < Complex.normSq (planarLinear a b p) ∧
        Complex.normSq (planarLinear a b p) < h} ∧
      ContMDiff 𝓘(ℝ,Euclidean d)
        (𝓘(ℝ,Euclidean d).prod 𝓘(ℝ,Euclidean d →L[ℝ] Euclidean d)) ∞
        (fun y => TotalSpace.mk' (Euclidean d →L[ℝ] Euclidean d) y
          (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,Euclidean d) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  sorry

end YauCounterexamples
end

end OAI
end
