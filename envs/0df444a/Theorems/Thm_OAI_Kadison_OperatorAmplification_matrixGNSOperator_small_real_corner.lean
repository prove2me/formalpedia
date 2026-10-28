-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_small_real_corner
-- name    : OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:51:05.056481+00:00
-- url     : https://prove2.me/theorems/e10e91ce-911a-4125-baf6-05d67d4a1663
-- title:
--   OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem matrixGNSOperator_small_real_corner (hQ : FactorCorner.IsFactor Q)
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
--       {c : ℝ} (hc : 0 ≤ c)
--       (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
--       (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
--       (htrace : (MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)).re≤(Fintype.card ι : ℝ)⁻¹)
--       (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
--       ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
--         (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖ ≤ c*‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_4` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.NormalSubalgebra.inclusion` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.OperatorAmplification.matrixGNSOperator` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067

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

namespace Kadison

namespace OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_4
variable (τ : M →ₚ[ℂ] ℂ)

theorem matrixGNSOperator_small_real_corner (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
    (f : matrixVonNeumann ι i₀ Q) (hf : IsStarProjection f)
    (htrace : (MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM f)).re≤(Fintype.card ι : ℝ)⁻¹)
    (X : CStarMatrix ι ι M) (hX : matrixInclusion ι i₀ M Q hQM f*X*matrixInclusion ι i₀ M Q hQM f=X) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖ ≤ c*‖X‖ := by
  sorry

end OperatorAmplification

end Kadison

end

end
end

end OAI
end
