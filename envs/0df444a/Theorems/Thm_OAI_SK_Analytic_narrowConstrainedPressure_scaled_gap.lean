-- Prove2me | Theorems.Thm_OAI_SK_Analytic_narrowConstrainedPressure_scaled_gap
-- name    : OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:58:15.441319+00:00
-- url     : https://prove2.me/theorems/82abdb7b-6a11-4a80-82f4-48c1d4266bb3
-- title:
--   OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScaledGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScaledGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped NNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem narrowConstrainedPressure_scaled_gap {β m : ℝ} (hβ : β≠0) (hm : 0 < m) :
--       ∃ ρ₀ c : ℝ, 0<ρ₀ ∧ 0 < c ∧ ∀ (α : StieltjesFunction ℝ),
--         (∀ z,α z∈Icc (0:ℝ) 1) → α 1=1 → ∀ (N : ℕ), 0<N →
--         ∀ ρ r q u δ : ℝ, 0<ρ → ρ≤ρ₀ → ρ^8 ≤ r → r+ρ≤q → q≤1 → r<u → u≤1 →
--         (∀ s∈Icc r u,scalarCDFOverlap β α s=s) → m≤α r →
--         scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q) →
--         |q-scalarCDFOverlap β α q|≤ρ^13 → α (r+ρ^8)-α (r-ρ^8)≤ρ^4 →
--         |δ|≤2*ρ^20 → Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
--         matrixConstrainedPressure N 3 β (tripleGram r δ q)≤3*scalarCDFParisi β α-c*ρ^3*δ^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.MatrixStates` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.tripleGram` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.scalarCDFOverlap` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.matrixConstrainedPressure` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.scalarCDFParisi` and `OAI.SK.Analytic.scalarCDFSusceptibilityAverage` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.main` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/NarrowScaledGap.lean (declaration OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowConstrainedPressure_scaled_gap {β m : ℝ} (hβ : β≠0) (hm : 0 < m) :
    ∃ ρ₀ c : ℝ, 0<ρ₀ ∧ 0 < c ∧ ∀ (α : StieltjesFunction ℝ),
      (∀ z,α z∈Icc (0:ℝ) 1) → α 1=1 → ∀ (N : ℕ), 0<N →
      ∀ ρ r q u δ : ℝ, 0<ρ → ρ≤ρ₀ → ρ^8 ≤ r → r+ρ≤q → q≤1 → r<u → u≤1 →
      (∀ s∈Icc r u,scalarCDFOverlap β α s=s) → m≤α r →
      scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q) →
      |q-scalarCDFOverlap β α q|≤ρ^13 → α (r+ρ^8)-α (r-ρ^8)≤ρ^4 →
      |δ|≤2*ρ^20 → Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
      matrixConstrainedPressure N 3 β (tripleGram r δ q)≤3*scalarCDFParisi β α-c*ρ^3*δ^2 := by
  sorry

end SK.Analytic

end
end

end OAI
end
