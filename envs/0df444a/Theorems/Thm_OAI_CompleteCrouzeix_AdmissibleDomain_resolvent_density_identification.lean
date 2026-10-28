-- Prove2me | Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_resolvent_density_identification
-- name    : OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:34:51.147981+00:00
-- url     : https://prove2.me/theorems/565f5dbb-97bd-472f-be40-322fd200164e
-- title:
--   OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification: intermediate lemma from OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification` of [lean/OAI/Analysis/NumericalRange/DensityIdentification.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/DensityIdentification.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CompleteCrouzeix.AdmissibleDomain`, with `open Set Filter Metric Complex MeasureTheory`, `open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker`):
--
--   ```lean
--   lemma resolvent_density_identification (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
--       {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
--       (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
--       (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
--         completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
--       {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
--       (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y) :
--       densityField (μ := AddCircle.haarAddCircle)
--         (hermitianField ⟨D.resolventField A,D.resolvent_continuous A hA⟩) X Y =
--         ((a/b:ℝ):ℂ) • D.cauchy.adjoint (densityField L X Y) +
--         ((b/a:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star (densityField L X Y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CompleteCrouzeix.AdmissibleDomain`, `OAI.CompleteCrouzeix.HSMatrix`, `OAI.CompleteCrouzeix.MatrixCircleL2`, `OAI.CompleteCrouzeix.densityField`, `OAI.CompleteCrouzeix.hermitianField`, `OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_15`, `OAI.CompleteCrouzeix.l2Star`, `OAI.CompleteCrouzeix.AdmissibleDomain.cauchy`, `OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_1`, `OAI.CompleteCrouzeix.AdmissibleDomain.resolventField`, `OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_continuous` and `OAI.CompleteCrouzeix.AdmissibleDomain.trace` (definitions bundle `OAIW2SC000` of this split); `OAI.CompleteCrouzeix.completeAnalyticEval` (the published bundle `Def_StructuralCrouzeix`).
--
--   **Used by.** The proof of `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound` of this split imports it.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NumericalRange/DensityIdentification.lean (declaration OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification)

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_251 u_252

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n : Type u_251} {m : Type u_252} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_1
lemma resolvent_density_identification (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y) :
    densityField (μ := AddCircle.haarAddCircle)
      (hermitianField ⟨D.resolventField A,D.resolvent_continuous A hA⟩) X Y =
      ((a/b:ℝ):ℂ) • D.cauchy.adjoint (densityField L X Y) +
      ((b/a:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star (densityField L X Y))) := by
  sorry
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end
