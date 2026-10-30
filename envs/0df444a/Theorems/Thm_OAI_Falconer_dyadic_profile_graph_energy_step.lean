-- Prove2me | Theorems.Thm_OAI_Falconer_dyadic_profile_graph_energy_step
-- name    : OAI.Falconer.dyadic_profile_graph_energy_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:48:02.473959+00:00
-- url     : https://prove2.me/theorems/0410e282-f0ce-4156-9aca-7e1f79247fbb
-- title:
--   OAI.Falconer.dyadic_profile_graph_energy_step: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.dyadic_profile_graph_energy_step` of [lean/OAI/MeasureTheory/Falconer/Graphs/ProfileGraphEstimate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Graphs/ProfileGraphEstimate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped SchwartzMap`):
--
--   ```lean
--   theorem dyadic_profile_graph_energy_step
--       (hpublished : PublishedGnomonicSurface) (n k : ℕ) (hn : 1 ≤ n)
--       (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
--       (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
--       (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
--       {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
--       (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
--       {α : ℝ} (hα : 0 < α) (T : ℝ) :
--       ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
--         ∀ (Q₁ Q₂ : DyadicCube (n+2)), Q₁.side = 1 → Q₂.side = 1 →
--         ∀ (ρ₁ ρ₂ : Measure (Space (n+2))) (N : ℕ) (s₁ s₂ lam : ℝ)
--           (m₁ m₂ : ℝ → ℝ),
--         Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁ →
--         Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂ → 0 < N →
--         ∀ (a p g₁ g₂ : ℕ) (σ : ℝ), a ≤ p → p ≤ N → 0 ≤ σ →
--         a ≤ g₁ → g₁ ≤ p → (g₁:ℝ)-a ≤ 2*σ*N →
--         a ≤ g₂ → g₂ ≤ p → (g₂:ℝ)-a ≤ 2*σ*N →
--         ∀ (X Y : List (Fin (n+2) → Bool)), X.length = a → Y.length = a →
--         ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
--         0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
--         Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side ≤ (τ/4)*D →
--         2*Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(p-a))+
--           8*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side) ≤ τ/4 →
--         4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ →
--         4*τ*((2:ℝ)^(p-a)/(Q₁.descendant X).side) ≤
--           (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ) →
--         ∀ {ι : Type*} (K : Finset ι) (w : ι → Sphere (n+2))
--           (η : ι → Sphere (n+2) → ℝ),
--         (∀ j ∈ K, ChartCapControl k (η j) (w j : Space (n+2)) δ H) →
--         (∀ j ∈ K, ∀ z, 0 ≤ η j z) → (∀ z, ∑ j ∈ K, η j z = 1) →
--         ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
--         ChartSymbolControl k b B D → ChartSymbolControl k c B D →
--         ∀ (W₁ W₂ : ℝ),
--         2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(g₁-a))) ≤ W₁ →
--         2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₂.descendant Y).side/(2:ℝ)^(g₂-a))) ≤ W₂ →
--         (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
--           ∀ᵐ x ∂ρ₁.restrict ((Q₁.descendant X).descendant q).carrier,
--           ∀ z : Sphere (n+2), b x z ≠ 0 →
--             DyadicParallelTest (Q₁.descendant X) ((Q₁.descendant X).occupiedPaths ρ₁ (p-a))
--               (g₁-a) q z W₁
--               ⌈((2:ℝ)^N)^(PlanarFalconer.height
--                 (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₁ p+
--                   1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
--         (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
--           ∀ᵐ x ∂ρ₂.restrict ((Q₂.descendant Y).descendant q).carrier,
--           ∀ z : Sphere (n+2), c x z ≠ 0 →
--             DyadicParallelTest (Q₂.descendant Y) ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))
--               (g₂-a) q z W₂
--               ⌈((2:ℝ)^N)^(PlanarFalconer.height
--                 (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₂ p+
--                   1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
--         ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
--         ∀ E : ℝ, 0 ≤ E →
--         (∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
--             (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
--           independentAngularEnergy p v Ψ
--             (fun z => endpointTransform
--               (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
--               (profileModelMass m₁ N p) b z.1 z.2)
--             (fun z => endpointTransform
--               (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
--               (profileModelMass m₂ N p) c z.1 z.2) ≤ E) →
--         independentAngularEnergy a v Ψ
--           (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant X).carrier)
--             (profileModelMass m₁ N a) b z.1 z.2)
--           (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant Y).carrier)
--             (profileModelMass m₂ N a) c z.1 z.2) ≤
--         2*11^(n+2)*((2:ℝ)^N)^(
--           -((m₁ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
--             (m₁ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))-
--           ((m₂ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
--             (m₂ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))+
--           (min (PlanarFalconer.height (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)
--             (PlanarFalconer.height (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)+
--           (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*σ)+4*(((n+2:ℕ):ℝ)+1)*lam)*E +
--         (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
--           ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
--             (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
--           capGraphError (n+2) k A C W ((2:ℝ)^N) T
--             (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
--             ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
--               (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.height` and `OAI.PlanarFalconer.sourceAngularShellMeasure` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.ChartCapControl`, `OAI.Falconer.ChartSymbolControl`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.DyadicParallelTest`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.capGraphError`, `OAI.Falconer.endpointTransform`, `OAI.Falconer.independentAngularEnergy`, `OAI.Falconer.profileModelMass`, `OAI.Falconer.DyadicCube.carrier`, `OAI.Falconer.DyadicCube.descendant`, `OAI.Falconer.DyadicCube.occupiedPaths` and `OAI.Falconer.Regularization.RegularizedProfileData` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_exists_jetState_graph_step`, `OAI.Falconer.exists_policy_prefix_common_budgets`, `OAI_Falconer_exists_two_profile_graph_step` and `OAI.Falconer.exists_uniform_outer_angular_decay` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Graphs/ProfileGraphEstimate.lean (declaration OAI.Falconer.dyadic_profile_graph_energy_step)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_profile_graph_energy_step
    (hpublished : PublishedGnomonicSurface) (n k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (n+2))) (N : ℕ) (s₁ s₂ lam : ℝ)
        (m₁ m₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂ → 0 < N →
      ∀ (a p g₁ g₂ : ℕ) (σ : ℝ), a ≤ p → p ≤ N → 0 ≤ σ →
      a ≤ g₁ → g₁ ≤ p → (g₁:ℝ)-a ≤ 2*σ*N →
      a ≤ g₂ → g₂ ≤ p → (g₂:ℝ)-a ≤ 2*σ*N →
      ∀ (X Y : List (Fin (n+2) → Bool)), X.length = a → Y.length = a →
      ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(p-a))+
        8*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side) ≤ τ/4 →
      4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ →
      4*τ*((2:ℝ)^(p-a)/(Q₁.descendant X).side) ≤
        (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ) →
      ∀ {ι : Type*} (K : Finset ι) (w : ι → Sphere (n+2))
        (η : ι → Sphere (n+2) → ℝ),
      (∀ j ∈ K, ChartCapControl k (η j) (w j : Space (n+2)) δ H) →
      (∀ j ∈ K, ∀ z, 0 ≤ η j z) → (∀ z, ∑ j ∈ K, η j z = 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl k b B D → ChartSymbolControl k c B D →
      ∀ (W₁ W₂ : ℝ),
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(g₁-a))) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₂.descendant Y).side/(2:ℝ)^(g₂-a))) ≤ W₂ →
      (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
        ∀ᵐ x ∂ρ₁.restrict ((Q₁.descendant X).descendant q).carrier,
        ∀ z : Sphere (n+2), b x z ≠ 0 →
          DyadicParallelTest (Q₁.descendant X) ((Q₁.descendant X).occupiedPaths ρ₁ (p-a))
            (g₁-a) q z W₁
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₁ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        ∀ᵐ x ∂ρ₂.restrict ((Q₂.descendant Y).descendant q).carrier,
        ∀ z : Sphere (n+2), c x z ≠ 0 →
          DyadicParallelTest (Q₂.descendant Y) ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))
            (g₂-a) q z W₂
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₂ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      ∀ E : ℝ, 0 ≤ E →
      (∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
          (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform
            (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform
            (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2) ≤ E) →
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant X).carrier)
          (profileModelMass m₁ N a) b z.1 z.2)
        (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant Y).carrier)
          (profileModelMass m₂ N a) c z.1 z.2) ≤
      2*11^(n+2)*((2:ℝ)^N)^(
        -((m₁ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₁ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))-
        ((m₂ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₂ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))+
        (min (PlanarFalconer.height (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)
          (PlanarFalconer.height (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)+
        (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*σ)+4*(((n+2:ℕ):ℝ)+1)*lam)*E +
      (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError (n+2) k A C W ((2:ℝ)^N) T
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
          ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
            (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card := by
  sorry

end Falconer

end OAI
end
