-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_finite_standard_compression_bound
-- name    : OAI.Kadison.NormalRepresentation.finite_standard_compression_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:54.615696+00:00
-- url     : https://prove2.me/theorems/a1d13a49-1214-42ea-a75c-5b74b4da437b
-- title:
--   OAI.Kadison.NormalRepresentation.finite_standard_compression_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped ComplexOrder InnerProductSpace`, `open OperatorAmplification`):
--
--   ```lean
--   theorem finite_standard_compression_bound [TopologicalSpace.SeparableSpace τ.GNS]
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
--       (T : H →L[ℂ] SumSpace (H:=τ.GNS) ι) (hcon : ‖T‖≤1)
--       (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=
--         (diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)).comp T)
--       (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
--       (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
--       ‖diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))*matrixOperator h X-
--         matrixOperator h X*diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))‖≤
--         (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.commutatorSeminorm`, `OAI.Kadison.diagonalAmplification` and `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalRepresentation

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

variable (ι : Type) [Fintype ι] [Nonempty ι]

theorem finite_standard_compression_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (T : H →L[ℂ] SumSpace (H:=τ.GNS) ι) (hcon : ‖T‖≤1)
    (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=
      (diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)).comp T)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  sorry

end Kadison.NormalRepresentation

end

end OAI
end
