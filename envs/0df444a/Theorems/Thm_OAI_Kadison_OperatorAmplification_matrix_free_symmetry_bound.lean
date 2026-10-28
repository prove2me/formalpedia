-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrix_free_symmetry_bound
-- name    : OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:53:00.676879+00:00
-- url     : https://prove2.me/theorems/3796a8c7-06c4-470f-b9d9-f9405d6dadd8
-- title:
--   OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open TracialSequence FreeMoments`):
--
--   ```lean
--   theorem matrix_free_symmetry_bound (hQ : FactorCorner.IsFactor Q)
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
--       {c : ℝ} (hc : 0 ≤ c)
--       (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
--       (s : unitary (CStarMatrix ι ι M)) (hs0 : (MatrixGNS.trace (ι:=ι) τ) (s:CStarMatrix ι ι M)=0)
--       (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
--       ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
--         MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖≤1040*c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.MatrixGNS.ArraySpace` and `OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.OperatorAmplification.matrixFreeSymmetryDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.NormalSubalgebra.inclusion` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixGNS.representation` (definitions bundle `OAIQ039C039` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.square_symmetry_after_average` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.OperatorAmplification

open TracialSequence FreeMoments

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixFreeSymmetryDecidableEq
variable (τ : M →ₚ[ℂ] ℂ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω (matrixVonNeumann ι i₀ Q) (matrixInclusion ι i₀ M Q hQM))

include hω F in
theorem matrix_free_symmetry_bound (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
    (s : unitary (CStarMatrix ι ι M)) (hs0 : (MatrixGNS.trace (ι:=ι) τ) (s:CStarMatrix ι ι M)=0)
    (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
      MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖≤1040*c := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
