-- Prove2me | Theorems.Thm_OAI_SKGap_scalar_closed_isolation_s2
-- name    : OAI.SKGap.scalar_closed_isolation_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:31.518951+00:00
-- url     : https://prove2.me/theorems/f107f8c7-cc9c-490f-8437-89df0f2e4107
-- title:
--   OAI.SKGap.scalar_closed_isolation_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter`, `open scoped NNReal ENNReal Topology`, `open Real Set`, `open MeasureTheory ProbabilityTheory Real Set Filter`, `open scoped Topology NNReal ENNReal BoundedContinuousFunction`, `open MeasureTheory ProbabilityTheory Filter Set Topology Real`, `open scoped NNReal ENNReal BoundedContinuousFunction`, `open Set Filter Topology`, `open MeasureTheory ProbabilityTheory Filter Set Topology Real`, `open scoped NNReal ENNReal BoundedContinuousFunction`, `open MeasureTheory ProbabilityTheory Filter Set Topology Real`, `open scoped NNReal ENNReal BoundedContinuousFunction`, `open MeasureTheory ProbabilityTheory Filter Set Topology Real`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem scalar_closed_isolation_s2 {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
--       (hT : 0 ≤ T) (hsmin : 0 < smin) {C : Set ScalarPoint} (hC : IsClosed C)
--       (hne : ∀ p ∈ C, p.2.1 ∈ Icc 0 T → p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
--       ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T,
--         ∀ σ ∈ Icc 0 (min δ 1), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
--         (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∈ C) →
--         (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
--         (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
--           ENNReal.ofReal (exp (-a*(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.ScalarPoint`, `OAI.SKGap.scalarCurve`, `OAI.SKGap.scalarEmpirical`, `OAI.SKGap.scalarIntegrand` and `OAI.SKGap.scalarS` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A000

section

attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

theorem scalar_closed_isolation_s2 {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 ≤ T) (hsmin : 0 < smin) {C : Set ScalarPoint} (hC : IsClosed C)
    (hne : ∀ p ∈ C, p.2.1 ∈ Icc 0 T → p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T,
      ∀ σ ∈ Icc 0 (min δ 1), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∈ C) →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  sorry

end SKGap

end
end
end
end
end
end
end
end

end OAI
end
