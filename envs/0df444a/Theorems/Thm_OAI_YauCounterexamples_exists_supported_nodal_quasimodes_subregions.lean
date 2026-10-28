-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_supported_nodal_quasimodes_subregions
-- name    : OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:05:21.847918+00:00
-- url     : https://prove2.me/theorems/e93b0596-a836-4415-8110-91c20565899b
-- title:
--   OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions` of [lean/OAI/Geometry/SmoothYau/NodalMeasure/ExistsSupportedBoxNodalQuasimodes.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/NodalMeasure/ExistsSupportedBoxNodalQuasimodes.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold`, `open scoped Topology ContDiff`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ENNReal NNReal`, `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_supported_nodal_quasimodes_subregions
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
--       ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
--       ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
--       (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
--       (∀ x ∈ K, fderiv ℝ φ x = 0 →
--         ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
--       ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
--       ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
--         ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
--           ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
--           ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
--           ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
--           (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
--           (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
--           (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
--           (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
--           ∀ R : Set NormalWaveSpace, R ⊆ K →
--           (∀ y ∈ R, |w y| ≤ c₀*Real.exp (n*φ y)) →
--           ∀ (J : Type) [Fintype J] (P Cₛ : J → Set (Fin 3 → ℝ)) (ℓ : J → ℝ),
--           (∀ a, 0 < ℓ a) → (∀ a, IsOpen (P a)) → (∀ a, Convex ℝ (P a)) →
--           (Pairwise fun a b => Disjoint (P a) (P b)) →
--           (∀ a, MeasurableSet (Cₛ a)) → (∀ a, IsFiniteMeasure (volume.restrict (Cₛ a))) →
--           (∀ a, normalWaveEquiv '' P a ⊆ R) →
--           (∀ a, ∀ x ∈ Cₛ a, x ∈ P a ∧
--             profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a ∧
--             ℓ a ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
--             ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a)) ∈ P a) →
--           0 < ∑ a, ℓ a*(volume (Cₛ a)).toReal →
--           ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
--             (∀ x : NormalWaveSpace, ∀ j ≤ m,
--               ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
--               ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
--                 C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
--             (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
--             ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
--               SignTests.signCertificate P (fun a => ε/(n*ℓ a)) ((w+u) ∘ normalWaveEquiv) ∧
--             ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
--               36*Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | (w+u) (normalWaveEquiv x)=0})
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.normalWaveEquiv` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_supported_box_nodal_quasimodes_subregions` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/NodalMeasure/ExistsSupportedBoxNodalQuasimodes.lean (declaration OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_supported_nodal_quasimodes_subregions
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ R : Set NormalWaveSpace, R ⊆ K →
        (∀ y ∈ R, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (J : Type) [Fintype J] (P Cₛ : J → Set (Fin 3 → ℝ)) (ℓ : J → ℝ),
        (∀ a, 0 < ℓ a) → (∀ a, IsOpen (P a)) → (∀ a, Convex ℝ (P a)) →
        (Pairwise fun a b => Disjoint (P a) (P b)) →
        (∀ a, MeasurableSet (Cₛ a)) → (∀ a, IsFiniteMeasure (volume.restrict (Cₛ a))) →
        (∀ a, normalWaveEquiv '' P a ⊆ R) →
        (∀ a, ∀ x ∈ Cₛ a, x ∈ P a ∧
          profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
          ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a)) ∈ P a) →
        0 < ∑ a, ℓ a*(volume (Cₛ a)).toReal →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            SignTests.signCertificate P (fun a => ε/(n*ℓ a)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            36*Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  sorry

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
open BoxIntegral

end YauCounterexamples
end

end OAI
end
