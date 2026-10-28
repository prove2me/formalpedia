-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrix_small_corner_bound
-- name    : OAI.Kadison.OperatorAmplification.matrix_small_corner_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:53:46.997728+00:00
-- url     : https://prove2.me/theorems/753ad404-2782-4cad-a76c-f427b3b30c85
-- title:
--   OAI.Kadison.OperatorAmplification.matrix_small_corner_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem matrix_small_corner_bound (hQ : FactorCorner.IsFactor Q)
--       (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
--       (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0) (h1 : σ 1=1)
--       (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
--       (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
--         ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
--       {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ a : M,‖T*ρ a-ρ a*T‖ ≤ c*‖a‖)
--       (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
--       (htrace : matrixTrace ι i₀ Q σ f≤(Fintype.card ι : ℂ)⁻¹)
--       (X : CStarMatrix ι ι M)
--       (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
--       ‖diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ X-
--         CyclicColumns.matrixRepresentation ρ X*diagonal (H:=K) ι T‖ ≤ c*‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CyclicColumns.instDecidableEq_solutions` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1` and `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_2` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.CyclicColumns.matrixRepresentation`, `OAI.Kadison.NormalSubalgebra.inclusion` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.OperatorAmplification.matrixTrace` (definitions bundle `OAIQ039C068` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C068

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_2
theorem matrix_small_corner_bound (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0) (h1 : σ 1=1)
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : ∀ q : Q,T*ρ (NormalSubalgebra.inclusion M Q hQM q)=
      ρ (NormalSubalgebra.inclusion M Q hQM q)*T)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ a : M,‖T*ρ a-ρ a*T‖ ≤ c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : matrixTrace ι i₀ Q σ f≤(Fintype.card ι : ℂ)⁻¹)
    (X : CStarMatrix ι ι M)
    (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖diagonal (H:=K) ι T*CyclicColumns.matrixRepresentation ρ X-
      CyclicColumns.matrixRepresentation ρ X*diagonal (H:=K) ι T‖ ≤ c*‖X‖ := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
