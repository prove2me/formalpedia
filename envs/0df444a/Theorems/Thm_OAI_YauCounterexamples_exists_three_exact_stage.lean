-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_exact_stage
-- name    : OAI.YauCounterexamples.exists_three_exact_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:32.322416+00:00
-- url     : https://prove2.me/theorems/31e9315e-809f-4f9b-9a2e-b35aff884edb
-- title:
--   OAI.YauCounterexamples.exists_three_exact_stage: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_exact_stage` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric BoxIntegral`, `open scoped Topology ContDiff ENNReal InnerProductSpace`):
--
--   ```lean
--   theorem exists_three_exact_stage :
--       ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--         IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
--         ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
--         ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
--         (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--           g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
--         ∀ V : Set (SmoothMetric ThreeModel ThreeManifold), IsSmoothNeighborhood g V →
--       ∃ e : ℝ, b<e ∧ e<R/2 ∧ ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆closedBall 0 a ∧
--       ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--         (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
--       ∀ᶠ n : ℕ in atTop, ∃ ĝ∈V, ∃ u : ThreeManifold → ℝ,
--         ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧
--         (∀ q, -laplaceBeltrami ĝ u q=productFrequency n*u q) ∧
--         (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0) ∧
--         (∀ q∉threeNormalInv '' closedBall 0 e,
--           (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=threeCoupled threeCouplingRadius n q) ∧
--         ENNReal.ofReal (A*productWaveFrequency n)<SignTests.signCertificate
--           (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val)
--           (fun j => ε/(productWaveFrequency n*ℓ j.val))
--           ((u ∘ threeNormalInv) ∘ normalWaveEquiv)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency`, `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_simple_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean (declaration OAI.YauCounterexamples.exists_three_exact_stage)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

theorem exists_three_exact_stage :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∀ V : Set (SmoothMetric ThreeModel ThreeManifold), IsSmoothNeighborhood g V →
    ∃ e : ℝ, b<e ∧ e<R/2 ∧ ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆closedBall 0 a ∧
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ∈V, ∃ u : ThreeManifold → ℝ,
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=productFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0) ∧
      (∀ q∉threeNormalInv '' closedBall 0 e,
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=threeCoupled threeCouplingRadius n q) ∧
      ENNReal.ofReal (A*productWaveFrequency n)<SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val)
        (fun j => ε/(productWaveFrequency n*ℓ j.val))
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) := by
  sorry

end YauCounterexamples
end

end OAI
end
