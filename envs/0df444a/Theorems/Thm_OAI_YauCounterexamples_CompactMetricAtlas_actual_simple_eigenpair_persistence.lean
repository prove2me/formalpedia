-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_actual_simple_eigenpair_persistence
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:30.94074+00:00
-- url     : https://prove2.me/theorems/634f7bcb-6bd3-4c99-8ed3-bf08f9292b39
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence` of [lean/OAI/Geometry/SmoothYau/Spectrum/SphericalSimpleEigenpairOpen.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/SphericalSimpleEigenpairOpen.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem actual_simple_eigenpair_persistence
--       (I : MetricIntegralAtlas (E:=E) (M:=M))
--       (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
--       (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
--       (lam : ℝ) (hn : α+lam ≠ 0)
--       (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
--       (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
--       (hsimple : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
--         (∀ x, -laplaceBeltrami g v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
--       (q : P → SmoothMetric E M) (p₀ : P) (hq0 : q p₀ = g)
--       (hq : ∀ i j l, ContinuousSmoothFamilyOn
--         (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target) :
--       ∃ (e : P → ℝ) (w : P → A.realH (2*((k+1:ℕ):ℝ))),
--         e p₀ = lam ∧ A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) = u ∧
--         ContinuousAt e p₀ ∧ ContinuousAt w p₀ ∧
--         ∀ᶠ p in 𝓝 p₀,
--           ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) ∧
--           A.realValue (2*((k+1:ℕ):ℝ)) (w p) ≠ 0 ∧
--           ∀ x, -laplaceBeltrami (q p) (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) x =
--             e p*A.realValue (2*((k+1:ℕ):ℝ)) (w p) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.CompactMetricAtlas.H`, `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients`, `OAI.YauCounterexamples.CompactMetricAtlas.p` and `OAI.YauCounterexamples.LocalMetricInverse` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.ContinuousSmoothFamilyOn` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.errorBound`, `OAI.YauCounterexamples.CompactMetricAtlas.realH` and `OAI.YauCounterexamples.CompactMetricAtlas.realValue` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.laplaceBeltrami` and `OAI.YauCounterexamples.metricCoefficients` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_three_fixed_witnesses` and `OAI.YauCounterexamples.spherical_largeWitness_eventually` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/SphericalSimpleEigenpairOpen.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

local instance (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul,mul_comm]⟩
theorem actual_simple_eigenpair_persistence
    (I : MetricIntegralAtlas (E:=E) (M:=M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    (hsimple : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami g v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (q : P → SmoothMetric E M) (p₀ : P) (hq0 : q p₀ = g)
    (hq : ∀ i j l, ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target) :
    ∃ (e : P → ℝ) (w : P → A.realH (2*((k+1:ℕ):ℝ))),
      e p₀ = lam ∧ A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) = u ∧
      ContinuousAt e p₀ ∧ ContinuousAt w p₀ ∧
      ∀ᶠ p in 𝓝 p₀,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) ∧
        A.realValue (2*((k+1:ℕ):ℝ)) (w p) ≠ 0 ∧
        ∀ x, -laplaceBeltrami (q p) (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) x =
          e p*A.realValue (2*((k+1:ℕ):ℝ)) (w p) x := by
  sorry
end CompactMetricAtlas
end

open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal

end YauCounterexamples
end

end OAI
end
