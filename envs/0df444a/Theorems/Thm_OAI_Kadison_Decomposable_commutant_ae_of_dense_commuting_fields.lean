-- Prove2me | Theorems.Thm_OAI_Kadison_Decomposable_commutant_ae_of_dense_commuting_fields
-- name    : OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:58.291263+00:00
-- url     : https://prove2.me/theorems/cf788318-99f1-406a-b678-f21047db21e6
-- title:
--   OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.Decomposable`, with `open MeasureTheory Filter`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem commutant_ae_of_dense_commuting_fields
--       (Q R : Ω → VonNeumannAlgebra H)
--       (T S : ℕ → Ω → H →L[ℂ] H)
--       (hT : ∀ n ξ,AEStronglyMeasurable (fun a => T n a ξ) μ)
--       (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
--       (hTb : ∀ n,∀ᵐ a ∂μ,‖T n a‖≤1) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤1)
--       (hcomm : ∀ i j,Commute (operator μ (T i) (hT i) (hTb i))
--         (operator μ (S j) (hS j) (hSb j)))
--       (hTd : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
--         ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => T (k n) a ξ) atTop (𝓝 (A ξ)))
--       (hSd : ∀ᵐ a ∂μ,∀ B : H →L[ℂ] H,B∈R a → ‖B‖≤1 →
--         ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => S (k n) a ξ) atTop (𝓝 (B ξ))) :
--       ∀ᵐ a ∂μ,R a≤(Q a).commutant
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Decomposable.operator` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.Decomposable.uniform_commutator_in_central_model` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem commutant_ae_of_dense_commuting_fields
    (Q R : Ω → VonNeumannAlgebra H)
    (T S : ℕ → Ω → H →L[ℂ] H)
    (hT : ∀ n ξ,AEStronglyMeasurable (fun a => T n a ξ) μ)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    (hTb : ∀ n,∀ᵐ a ∂μ,‖T n a‖≤1) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤1)
    (hcomm : ∀ i j,Commute (operator μ (T i) (hT i) (hTb i))
      (operator μ (S j) (hS j) (hSb j)))
    (hTd : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => T (k n) a ξ) atTop (𝓝 (A ξ)))
    (hSd : ∀ᵐ a ∂μ,∀ B : H →L[ℂ] H,B∈R a → ‖B‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => S (k n) a ξ) atTop (𝓝 (B ξ))) :
    ∀ᵐ a ∂μ,R a≤(Q a).commutant := by
  sorry

end Kadison.Decomposable

end

end
end

end OAI
end
