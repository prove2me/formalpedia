-- Prove2me | Theorems.Thm_OAI_Falconer_centered_packet_product_power
-- name    : OAI.Falconer.centered_packet_product_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:42:07.550213+00:00
-- url     : https://prove2.me/theorems/b197e292-d1b1-4667-ab3d-e0ab694034b7
-- title:
--   OAI.Falconer.centered_packet_product_power: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.centered_packet_product_power` of [lean/OAI/MeasureTheory/Falconer/Estimates/CenteredPacketPower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/CenteredPacketPower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`):
--
--   ```lean
--   theorem centered_packet_product_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
--       ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
--         let Δ := 4*(1/2:ℝ)^N
--         let D := Real.exp (ε*(N:ℝ)*Real.log 2)
--         ∀ (s c b : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
--           (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (NP : ℕ),
--         let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
--         let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
--         κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
--         (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt Δ (P y) ∧
--           NormalizedFiniteBallBound Δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
--           (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
--         (∀ y ∈ Y, ∀ x ∈ P y, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-y| ≤ Δ) →
--         (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
--           NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
--           L ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U ∧
--           ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
--         (∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
--           scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
--         Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.FiniteSeparatedAt`, `OAI.Falconer.NormalizedFiniteBallBound`, `OAI.Falconer.Space` and `OAI.Falconer.TubeIncident` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.scalarBallMass` (definitions bundle `OAIQ088F001` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.frozen_coarse_packet_impossible` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/CenteredPacketPower.lean (declaration OAI.Falconer.centered_packet_product_power)

import Mathlib
import Definitions.Def_OAIQ088F000
import Definitions.Def_OAIQ088F001

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_product_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let Δ := 4*(1/2:ℝ)^N
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (s c b : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
        (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (NP : ℕ),
      let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
      let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
      κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt Δ (P y) ∧
        NormalizedFiniteBallBound Δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-y| ≤ Δ) →
      (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
        L ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U ∧
        ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ) := by
  sorry

end Falconer

end OAI
end
