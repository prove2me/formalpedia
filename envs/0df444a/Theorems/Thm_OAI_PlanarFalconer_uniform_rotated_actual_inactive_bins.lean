-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_rotated_actual_inactive_bins
-- name    : OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:24.856306+00:00
-- url     : https://prove2.me/theorems/c12bcce7-ce25-46bb-b123-a8464bb54958
-- title:
--   OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedActualInactive.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedActualInactive.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff ComplexConjugate`):
--
--   ```lean
--   theorem uniform_rotated_actual_inactive_bins {w : ℝ → ℂ}
--       (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
--       {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c)
--       (K₁ K₂ : ℕ) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
--       κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
--       (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
--       ∀ (e : UnitCircle) (φ axis : ℝ), |φ| ≤ Real.pi →
--       dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
--       (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
--       ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
--       ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
--         (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
--       S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
--       S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
--       (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
--       ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
--       ∀ (ρ₁ ρ₂ : Measure Plane) (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
--         (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ) (x y : Plane), ‖h₁ x‖ ≤ 1 → ‖h₂ y‖ ≤ 1 →
--       let f := fun θ =>
--         inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁ x (sourceUnitDirection (θ+axis)) *
--         conj (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂ y (sourceUnitDirection (θ+axis)))
--       ((2 : ℝ)^N)^outer * ‖∫ θ : ℝ, cosineOscillator Λ (θ-φ) *
--         (w θ * selectedBinAmplitude (graphUncappedAngularScale N sig t)
--           (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
--             (3*graphUncappedAngularScale N sig t)) f θ)‖ ≤ ((2 : ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularBinCount`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.graphUncappedAngularScale`, `OAI.PlanarFalconer.inheritedCircleSymbol` and `OAI.PlanarFalconer.sourceUnitDirection` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.cosineOscillator` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.inactiveAngularLabels` and `OAI.PlanarFalconer.selectedBinAmplitude` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_parent_discarded_F` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedActualInactive.lean (declaration OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_rotated_actual_inactive_bins {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
    ∀ (e : UnitCircle) (φ axis : ℝ), |φ| ≤ Real.pi →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ) (x y : Plane), ‖h₁ x‖ ≤ 1 → ‖h₂ y‖ ≤ 1 →
    let f := fun θ =>
      inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁ x (sourceUnitDirection (θ+axis)) *
      conj (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂ y (sourceUnitDirection (θ+axis)))
    ((2 : ℝ)^N)^outer * ‖∫ θ : ℝ, cosineOscillator Λ (θ-φ) *
      (w θ * selectedBinAmplitude (graphUncappedAngularScale N sig t)
        (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
          (3*graphUncappedAngularScale N sig t)) f θ)‖ ≤ ((2 : ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
