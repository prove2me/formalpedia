-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_SparseGrowth_HasPolynomialDegree_linear_virtually_indicable
-- name    : OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:00.658809+00:00
-- url     : https://prove2.me/theorems/824b2299-cb44-4a0e-bbf4-5f50580cce0f
-- title:
--   OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable` of [lean/OAI/Probability/CriticalPercolation/Harmonic/WeakGromovHarmonic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/WeakGromovHarmonic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.SparseGrowth`, with `open Set Function`, `open scoped Classical`):
--
--   ```lean
--   lemma HasPolynomialDegree.linear_virtually_indicable {A : Type*} [Group A] [DecidableEq A]
--       {d : ℕ} (hg : HasPolynomialDegree A d) [Infinite A] :
--       ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree` (definitions bundle `OAIQ228B001` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality` and `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/WeakGromovHarmonic.lean (declaration OAI.CriticalPercolation.SparseGrowth.HasPolynomialDegree.linear_virtually_indicable)

import Mathlib
import Definitions.Def_OAIQ228B001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth

lemma HasPolynomialDegree.linear_virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  sorry

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end
