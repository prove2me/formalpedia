-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_actual_graph_amplitude_E
-- name    : OAI.PlanarFalconer.uniform_actual_graph_amplitude_E
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:02:36.209007+00:00
-- url     : https://prove2.me/theorems/9c1990b1-86b3-4e25-b63a-0e8dc0b42c7e
-- title:
--   OAI.PlanarFalconer.uniform_actual_graph_amplitude_E: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_actual_graph_amplitude_E` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphNonedgeAmplitude.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphNonedgeAmplitude.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem uniform_actual_graph_amplitude_E {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
--       ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
--       ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
--       (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
--       ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
--       ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
--       ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
--       (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
--       (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ t u : ℝ, 0 ≤ u →
--       t ≤ u+2*sig*(N:ℝ) → (L:ℝ) ≤ u+2*sig*(N:ℝ) →
--       ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
--       let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
--         N lam sig J i (h a)
--       GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig t c₀) j₁ j₂ Ψ)
--         A (graphNonedgeDerivativeScale N sig u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.GraphDerivativeBound`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.UnitCircle`, `OAI.PlanarFalconer.descriptorLength` and `OAI.PlanarFalconer.inheritedCircleSymbol` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.graphNonedgeDerivativeScale` (definitions bundle `OAIQ038F001` of this split); `OAI.PlanarFalconer.graphAmplitudePullback` and `OAI.PlanarFalconer.graphAngularScale` (definitions bundle `OAIQ038F002` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_actual_graph_nonedge_power` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/GraphNonedgeAmplitude.lean (declaration OAI.PlanarFalconer.uniform_actual_graph_amplitude_E)

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

theorem uniform_actual_graph_amplitude_E {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ t u : ℝ, 0 ≤ u →
    t ≤ u+2*sig*(N:ℝ) → (L:ℝ) ≤ u+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a)
    GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig t c₀) j₁ j₂ Ψ)
      A (graphNonedgeDerivativeScale N sig u) := by
  sorry

end PlanarFalconer

end OAI
end
