-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ParameterHierarchy_eventually_reciprocal_code_budget
-- name    : OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:48:30.509237+00:00
-- url     : https://prove2.me/theorems/fe1012c4-6bcd-4d55-861e-3cdda470721a
-- title:
--   OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget` of [lean/OAI/Combinatorics/RamseyFive/Entropy/ReciprocalCodeNumerics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/ReciprocalCodeNumerics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ParameterHierarchy`, with `open Filter Real Marking ProjectiveIncidence`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_reciprocal_code_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
--       ∀ᶠ σ : ℝ in atTop,∀ (q D R k : ℝ) (w H l : ℕ),
--         Real.exp σ=q→Range η σ D R→1≤H→(H:ℝ)≤σ^beta η→
--         (w:ℝ)*D≤σ^(1+η/2)→q*σ^(1+η)≤2*k→(l:ℝ)≤q*σ^(1+η)→
--         windowCodeBudget σ q (P η σ D R) (D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4) w H+
--             (w+1)*Real.log (l+1)≤k*D*σ^(-η/3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta` and `OAI.SharpRamseyFive.ProjectiveIncidence.windowCodeBudget` (definitions bundle `OAIQ060R001` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/ReciprocalCodeNumerics.lean (declaration OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget)

import Mathlib
import Definitions.Def_OAIQ060R001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence
open scoped Topology
noncomputable section

theorem eventually_reciprocal_code_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D R k : ℝ) (w H l : ℕ),
      Real.exp σ=q→Range η σ D R→1≤H→(H:ℝ)≤σ^beta η→
      (w:ℝ)*D≤σ^(1+η/2)→q*σ^(1+η)≤2*k→(l:ℝ)≤q*σ^(1+η)→
      windowCodeBudget σ q (P η σ D R) (D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)≤k*D*σ^(-η/3) := by
  sorry
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end
