-- Prove2me | Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_ordered_modules
-- name    : OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:34:56.412258+00:00
-- url     : https://prove2.me/theorems/d01ee509-b689-4977-8426-5d3b921af2ee
-- title:
--   OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules: intermediate lemma from OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules` of [lean/OAI/Analysis/NumericalRange/OrderedDensities.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/OrderedDensities.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CompleteCrouzeix.AdmissibleDomain`, with `open Set Filter Metric Complex MeasureTheory`, `open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker`):
--
--   ```lean
--   lemma ordered_modules {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
--       (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1) :
--       ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
--         ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
--         (∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (D.trace F hF t*fromHS (u t))) ∧
--         (∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*D.trace F hF t)) ∧
--         D.cauchy.comp (L.comp D.cauchy) = L.comp D.cauchy ∧
--         D.cauchy.comp (R.comp D.cauchy) = R.comp D.cauchy
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompleteCrouzeix.AdmissibleDomain`, `OAI.CompleteCrouzeix.HSMatrix`, `OAI.CompleteCrouzeix.MatrixCircleL2`, `OAI.CompleteCrouzeix.fromHS`, `OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_15`, `OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56`, `OAI.CompleteCrouzeix.toHS`, `OAI.CompleteCrouzeix.AdmissibleDomain.cauchy` and `OAI.CompleteCrouzeix.AdmissibleDomain.trace` (definitions bundle `OAIW2SC000` of this split).
--
--   **Used by.** The proof of `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound` of this split imports it.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/OrderedDensities.lean (declaration OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules)

import Mathlib
import Definitions.Def_OAIW2SC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56
lemma ordered_modules {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1) :
    ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
      (∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (D.trace F hF t*fromHS (u t))) ∧
      (∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*D.trace F hF t)) ∧
      D.cauchy.comp (L.comp D.cauchy) = L.comp D.cauchy ∧
      D.cauchy.comp (R.comp D.cauchy) = R.comp D.cauchy := by
  sorry
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end
