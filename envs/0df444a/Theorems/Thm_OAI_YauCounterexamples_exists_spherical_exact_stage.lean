-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_exact_stage
-- name    : OAI.YauCounterexamples.exists_spherical_exact_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:40:43.878995+00:00
-- url     : https://prove2.me/theorems/588ce983-2bee-4f8b-b98d-5cfbe15dc2dd
-- title:
--   OAI.YauCounterexamples.exists_spherical_exact_stage: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_exact_stage` of [lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold BoxIntegral`, `open scoped Topology ContDiff ENNReal InnerProductSpace`):
--
--   ```lean
--   theorem exists_spherical_exact_stage
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
--       {t s r a b : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r)
--       (hra : r < a) (hab : a < b) (hb : b < 3/10)
--       {F : Set (Sphere 3)} (hF : IsClosed F)
--       (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
--         ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
--       (A : ℝ) (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g N) :
--       ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--         (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
--       ∀ᶠ n : ℕ in atTop, ∃ ĝ ∈ N, ∃ u : Sphere 3 → ℝ,
--         ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧
--         (∀ q, -laplaceBeltrami ĝ u q=sphereFrequency n*u q) ∧
--         (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm) (chartAt (Euclidean 3) q q) ≠ 0) ∧
--         (∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q →
--           (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=roundPower sourceAxisOne sourceAxisTwo n q) ∧
--         ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
--           (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val)
--           (fun j => ε/((n:ℝ)*ℓ j.val))
--           ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv`, `OAI.YauCounterexamples.selfMetricFlat`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole`, `OAI.YauCounterexamples.sourceSignBox`, `OAI.YauCounterexamples.sphericalCoverage`, `OAI.YauCounterexamples.sphericalRadius` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.sphereFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` and `OAI.YauCounterexamples.sphericalProfileMetricNeighborhood` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_simple_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean (declaration OAI.YauCounterexamples.exists_spherical_exact_stage)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace
namespace YauCounterexamples

theorem exists_spherical_exact_stage
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r a b : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r)
    (hra : r < a) (hab : a < b) (hb : b < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g N) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ ∈ N, ∃ u : Sphere 3 → ℝ,
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=sphereFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm) (chartAt (Euclidean 3) q q) ≠ 0) ∧
      (∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q →
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=roundPower sourceAxisOne sourceAxisTwo n q) ∧
      ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val)
        (fun j => ε/((n:ℝ)*ℓ j.val))
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  sorry

end YauCounterexamples
end

end OAI
end
