-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_regularized_original_graph_removal
-- name    : OAI.PlanarFalconer.uniform_regularized_original_graph_removal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:19.161007+00:00
-- url     : https://prove2.me/theorems/80a6c297-a57d-42b4-9006-55541917b13c
-- title:
--   OAI.PlanarFalconer.uniform_regularized_original_graph_removal: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_regularized_original_graph_removal` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphOriginalGraphRemoval.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphOriginalGraphRemoval.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_regularized_original_graph_removal {sig : ℝ} (hsig : 0 < sig)
--       (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
--       (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
--       {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
--       ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
--       ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
--       ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
--       ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
--       (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
--       ∀ (J i : ℕ) (h : Fin 4 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
--       ∀ (a : ℝ) (p : ℕ) (v : ℝ), 0 ≤ a → a ≤ p → p ≤ N →
--       0 ≤ v-p → (p:ℝ)-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) → v-a ≤ N →
--       ∀ (distance : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
--       X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
--       (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
--       ∀ (axis : ℝ) (I : Finset GraphNonedgeIndex),
--       I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
--       (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
--       let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
--         (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
--       let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
--       let M := fun l => ((2:ℝ)^N)^(-mass l p)
--       let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
--         distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
--       ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p • (∑ e ∈ I, F e)) -
--         ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
--           (∑ e ∈ graphRetainedIndices I N sig p distance Q q, F e))‖ ≤ ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.GraphCellQuadIndex`, `OAI.PlanarFalconer.GraphNonedgeIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.angularBinCount`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.graphQuadCells`, `OAI.PlanarFalconer.graphUncappedAngularScale`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.DyadicSquare.carrier` and `OAI.PlanarFalconer.DyadicSquare.center` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphProfileCoefficient` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.graphAngularScale`, `OAI.PlanarFalconer.graphAngularScale_pos`, `OAI.PlanarFalconer.graphChosenRepresentative`, `OAI.PlanarFalconer.graphNonedgeIndices`, `OAI.PlanarFalconer.graphOriginalTerm`, `OAI.PlanarFalconer.graphRetainedIndices` and `OAI.PlanarFalconer.graphSlotParent` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proofs of `OAI.PlanarFalconer.uniform_actual_product_H_graph` and `OAI.PlanarFalconer.uniform_actual_retained_distance_graph` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphOriginalGraphRemoval.lean (declaration OAI.PlanarFalconer.uniform_regularized_original_graph_removal)

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
open scoped ContDiff

theorem uniform_regularized_original_graph_removal {sig : ℝ} (hsig : 0 < sig)
    (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 4 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a : ℝ) (p : ℕ) (v : ℝ), 0 ≤ a → a ≤ p → p ≤ N →
    0 ≤ v-p → (p:ℝ)-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) → v-a ≤ N →
    ∀ (distance : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ (axis : ℝ) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
    (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l p)
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
      distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
    ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p • (∑ e ∈ I, F e)) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
        (∑ e ∈ graphRetainedIndices I N sig p distance Q q, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
