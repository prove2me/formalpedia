-- Prove2me | Theorems.Thm_OAI_Falconer_frozen_coarse_packet_impossible
-- name    : OAI.Falconer.frozen_coarse_packet_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:51:43.228251+00:00
-- url     : https://prove2.me/theorems/d5664b4e-aabc-459e-8392-82ef58e4830e
-- title:
--   OAI.Falconer.frozen_coarse_packet_impossible: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.frozen_coarse_packet_impossible` of [lean/OAI/MeasureTheory/Falconer/Incidence/FrozenCoarseObstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Incidence/FrozenCoarseObstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem frozen_coarse_packet_impossible {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
--       ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧
--       ∀ n : ℕ, N0 ≤ n+2 →
--         let Δ := 1/(2:ℝ)^n
--         let δ := 1/(2:ℝ)^(n+3)
--         let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
--         ∀ (s t m M mF MF L J B : ℝ) (C : Finset (Space 2))
--           (T P : Space 2 → Finset (Space 2))
--           (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
--           (G : Space 2 → Finset (Space 2)),
--         κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
--         0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
--         0 < L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
--         1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
--         C.Nonempty → InBoundedLineChart C → FiniteSeparatedAt δ C →
--         NormalizedFiniteBallBound δ t E C →
--         (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
--           InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
--           NormalizedFiniteBallBound δ s E (T x) ∧ ∀ a ∈ T x, TubeIncident δ x a) →
--         ((C.biUnion T).card:ℝ) ≤ L →
--         (∀ x ∈ C, (P x).Nonempty ∧
--           (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
--           NormalizedFiniteBallBound Δ t E ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
--         (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
--           FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s E (V x p) ∧
--           ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
--         (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
--         (∀ x ∈ C, ∀ a ∈ T x,
--           ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
--         (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
--         (∃ k : ℕ, ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) →
--         (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ E/(Δ^s)^4 → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.FiniteSeparatedAt`, `OAI.Falconer.InBoundedLineChart`, `OAI.Falconer.NormalizedFiniteBallBound`, `OAI.Falconer.Space` and `OAI.Falconer.TubeIncident` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.coarsePencilWeight` and `OAI.Falconer.localPacketPoint` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.bounded_chart_regular_fine_gain` and `OAI_Falconer_general_regular_coarse_cover_alternative` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Incidence/FrozenCoarseObstruction.lean (declaration OAI.Falconer.frozen_coarse_packet_impossible)

import Mathlib
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_coarse_packet_impossible {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t m M mF MF L J B : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 < L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      C.Nonempty → InBoundedLineChart C → FiniteSeparatedAt δ C →
      NormalizedFiniteBallBound δ t E C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s E (T x) ∧ ∀ a ∈ T x, TubeIncident δ x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t E ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s E (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      (∃ k : ℕ, ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) →
      (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ E/(Δ^s)^4 → False := by
  sorry

end Falconer

end OAI
end
