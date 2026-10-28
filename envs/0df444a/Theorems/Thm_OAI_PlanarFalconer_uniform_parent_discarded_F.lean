-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_parent_discarded_F
-- name    : OAI.PlanarFalconer.uniform_parent_discarded_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:23.189997+00:00
-- url     : https://prove2.me/theorems/a0150431-f59d-4fc8-b539-3d8dc4183093
-- title:
--   OAI.PlanarFalconer.uniform_parent_discarded_F: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_parent_discarded_F` of [lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ParentDiscardedForm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ParentDiscardedForm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_parent_discarded_F
--       {sig κ T : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
--       (K₁ K₂ : ℕ) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L n : ℕ) (a p v r : ℝ), p = a+n →
--       κ*(N : ℝ) ≤ p-a → p-a ≤ v-p+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ v-p →
--       (L : ℝ) ≤ v-p+2*sig*(N : ℝ) →
--       ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
--       X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
--       100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
--       dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
--       ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
--       Ψ (r/(2:ℝ)^v) ≠ 0 →
--       ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
--       ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
--         (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
--       S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
--       S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
--       (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
--       ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
--       ∀ (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂], ∀ (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
--         (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ),
--       Measurable h₁ → Measurable h₂ → (∀ x, ‖h₁ x‖ ≤ 1) → (∀ y, ‖h₂ y‖ ≤ 1) →
--       ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ →
--       ‖sourceCellwiseDistanceF X Y ρ₁ ρ₂ n n M₁ M₂
--         (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
--           sourceParentInactiveSelection N sig (p-a) X Y A B dir)
--         (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁)
--         (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂) r‖ ≤
--         ((2:ℝ)^N)^(-T) * ((ρ₁ X.carrier).toReal/M₁) * ((ρ₂ Y.carrier).toReal/M₂)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.sourceConeCircle`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.sourceCellwiseDistanceF` and `OAI.PlanarFalconer.sourceParentInactiveSelection` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_distance_HF_graph` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Recursion/ParentDiscardedForm.lean (declaration OAI.PlanarFalconer.uniform_parent_discarded_F)

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

theorem uniform_parent_discarded_F
    {sig κ T : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L n : ℕ) (a p v r : ℝ), p = a+n →
    κ*(N : ℝ) ≤ p-a → p-a ≤ v-p+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ v-p →
    (L : ℝ) ≤ v-p+2*sig*(N : ℝ) →
    ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
    Ψ (r/(2:ℝ)^v) ≠ 0 →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂], ∀ (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ),
    Measurable h₁ → Measurable h₂ → (∀ x, ‖h₁ x‖ ≤ 1) → (∀ y, ‖h₂ y‖ ≤ 1) →
    ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ →
    ‖sourceCellwiseDistanceF X Y ρ₁ ρ₂ n n M₁ M₂
      (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
        sourceParentInactiveSelection N sig (p-a) X Y A B dir)
      (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁)
      (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂) r‖ ≤
      ((2:ℝ)^N)^(-T) * ((ρ₁ X.carrier).toReal/M₁) * ((ρ₂ Y.carrier).toReal/M₂) := by
  sorry

end PlanarFalconer

end OAI
end
