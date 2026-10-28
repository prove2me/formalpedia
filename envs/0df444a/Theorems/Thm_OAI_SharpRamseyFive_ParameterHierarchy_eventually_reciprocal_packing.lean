-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ParameterHierarchy_eventually_reciprocal_packing
-- name    : OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:48:25.275788+00:00
-- url     : https://prove2.me/theorems/08f91fb5-45c6-41ad-b33f-e51d8f1e7162
-- title:
--   OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing` of [lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalDropNumerics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalDropNumerics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ParameterHierarchy`, with `open Filter Real Marking`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_reciprocal_packing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (c : ℝ) (hc : 0 < c) :
--       ∀ᶠ σ : ℝ in atTop,∀ (q D : ℝ) (m : ℕ),2≤q→σ^beta η≤D→D≤σ^(1-η/2)→
--         c*q*σ^(1+η)≤ m→(m:ℝ)≤q*σ^(1+η)→∀closed : Bool,
--         ∃ (w n rounds rem : ℕ),
--           0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
--           (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
--           (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
--           (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
--           0 < rounds ∧ 0 < rem ∧ n≤2*rem ∧ rem+rounds≤n ∧
--           q*D*σ^(3000*beta η)/2 ≤ rounds ∧ (n:ℝ)/2 ≤ rem
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ParameterHierarchy.beta` (definitions bundle `OAIQ060R001` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalDropNumerics.lean (declaration OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing)

import Mathlib
import Definitions.Def_OAIQ060R001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking
open scoped Topology
noncomputable section

theorem eventually_reciprocal_packing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D : ℝ) (m : ℕ),2≤q→σ^beta η≤D→D≤σ^(1-η/2)→
      c*q*σ^(1+η)≤ m→(m:ℝ)≤q*σ^(1+η)→∀closed : Bool,
      ∃ (w n rounds rem : ℕ),
        0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
        (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
        (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
        (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
        0 < rounds ∧ 0 < rem ∧ n≤2*rem ∧ rem+rounds≤n ∧
        q*D*σ^(3000*beta η)/2 ≤ rounds ∧ (n:ℝ)/2 ≤ rem := by
  sorry
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end
