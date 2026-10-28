-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_distance_HF_graph
-- name    : OAI.PlanarFalconer.uniform_actual_distance_HF_graph
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:02:13.372179+00:00
-- url     : https://prove2.me/theorems/10a9fda5-4c13-4f40-b2b0-f66f45c9a26a
-- title:
--   OAI.PlanarFalconer.uniform_actual_distance_HF_graph: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_distance_HF_graph` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceHFGraph.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceHFGraph.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_actual_distance_HF_graph
--       {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
--       (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
--       (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
--       ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
--       (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
--       ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
--       ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
--       ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
--       (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
--       ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
--       ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
--       10*sig*N ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
--       ∀ A B : CellPath, A.length = a → B.length = a →
--       100*(2:ℝ)^(-(a:ℝ)) ≤ dist ((Q 0).descendant A).center ((Q 1).descendant B).center →
--       dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
--       let X := (Q 0).descendant A
--       let Y := (Q 1).descendant B
--       let t : ℝ := (a+n:ℕ)-a
--       let θ := graphAngularScale N sig t c₀
--       let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B
--       let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
--         (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2
--         (sourceParentAxis X Y) e.1.1 e.1.2
--       let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
--       let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
--       let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 1,ρ 1,ρ 0]
--         (fun l => (graphQuadCells ![Q 0,Q 1,Q 1,Q 0] e.1 l).carrier)
--         ![M 0,M 1,M 1,M 0] ![β 0,β 1,β 1,β 0] true e.2.2 (sourceParentAxis X Y) θ v e.2.1.1 e.2.1.2 Ψ
--       ‖((sourceParentHF a v Ψ X Y (ρ 0) (ρ 1)
--           (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)).toReal : ℂ) -
--         ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) •
--           (∑ e ∈ graphRetainedIndices I N sig (a+n) true ![Q 0,Q 1,Q 1,Q 0] rep, F e))‖ ≤ ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.GraphCellQuadIndex`, `OAI.PlanarFalconer.GraphNonedgeIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.descriptorLength`, `OAI.PlanarFalconer.graphQuadCells`, `OAI.PlanarFalconer.graphUncappedAngularScale`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.sourceParentHF`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.center` and `OAI.PlanarFalconer.DyadicSquare.descendant` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphProfileCoefficient` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.graphAngularScale`, `OAI.PlanarFalconer.graphAngularScale_pos`, `OAI.PlanarFalconer.graphChosenRepresentative`, `OAI.PlanarFalconer.graphOriginalTerm`, `OAI.PlanarFalconer.graphRetainedIndices` and `OAI.PlanarFalconer.sourceParentGraphIndices` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_distance_equation12` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceHFGraph.lean (declaration OAI.PlanarFalconer.uniform_actual_distance_HF_graph)

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

theorem uniform_actual_distance_HF_graph
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
    10*sig*N ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    100*(2:ℝ)^(-(a:ℝ)) ≤ dist ((Q 0).descendant A).center ((Q 1).descendant B).center →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2
      (sourceParentAxis X Y) e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 1,ρ 1,ρ 0]
      (fun l => (graphQuadCells ![Q 0,Q 1,Q 1,Q 0] e.1 l).carrier)
      ![M 0,M 1,M 1,M 0] ![β 0,β 1,β 1,β 0] true e.2.2 (sourceParentAxis X Y) θ v e.2.1.1 e.2.1.2 Ψ
    ‖((sourceParentHF a v Ψ X Y (ρ 0) (ρ 1)
        (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)).toReal : ℂ) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) •
        (∑ e ∈ graphRetainedIndices I N sig (a+n) true ![Q 0,Q 1,Q 1,Q 0] rep, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
