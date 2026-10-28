-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_distance_degrees
-- name    : OAI.PlanarFalconer.uniform_actual_distance_degrees
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:01:42.749408+00:00
-- url     : https://prove2.me/theorems/6b2652de-32ed-442d-b564-edcc1b24ebdf
-- title:
--   OAI.PlanarFalconer.uniform_actual_distance_degrees: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_distance_degrees` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceDegrees.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceDegrees.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem uniform_actual_distance_degrees {sig κ c₀ : ℝ} (hsig : 0 < sig)
--       (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) {J : ℕ} (hJ : 0 < J) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
--       ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
--       ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
--       ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
--       ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
--       ∀ a n : ℕ, (∀ l, d l (e l) = .parallel a (a+n)) → a+n ≤ N → κ*N ≤ (n:ℝ) →
--       ∀ A B : CellPath, A.length = a → B.length = a →
--       dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
--       let t : ℝ := (a+n:ℕ)-a
--       let θ := graphAngularScale N sig t c₀
--       let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
--       let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
--         (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
--       let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
--       let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
--       ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
--       ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤
--         144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
--         (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.CellPath`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.GraphNonedgeIndex`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.activeDistanceMatrixNeighbors`, `OAI.PlanarFalconer.graphUncappedAngularScale`, `OAI.PlanarFalconer.height`, `OAI.PlanarFalconer.inheritedCircleSymbol`, `OAI.PlanarFalconer.sourceParentAxis`, `OAI.PlanarFalconer.DyadicSquare.center` and `OAI.PlanarFalconer.DyadicSquare.descendant` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphAngularScale`, `OAI.PlanarFalconer.graphAngularScale_pos`, `OAI.PlanarFalconer.graphChosenRepresentative` and `OAI.PlanarFalconer.sourceRetainedDistanceIndices` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_distance_equation12` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/ActualDistanceDegrees.lean (declaration OAI.PlanarFalconer.uniform_actual_distance_degrees)

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

theorem uniform_actual_distance_degrees {sig κ c₀ : ℝ} (hsig : 0 < sig)
    (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a n : ℕ, (∀ l, d l (e l) = .parallel a (a+n)) → a+n ≤ N → κ*N ≤ (n:ℝ) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
    ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
    ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤
      144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
      (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig) := by
  sorry

end PlanarFalconer

end OAI
end
