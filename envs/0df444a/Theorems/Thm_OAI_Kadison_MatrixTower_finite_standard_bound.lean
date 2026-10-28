-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_finite_standard_bound
-- name    : OAI.Kadison.MatrixTower.finite_standard_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:41:09.074118+00:00
-- url     : https://prove2.me/theorems/5ab85fc7-9d8b-4501-bf67-f90249a73dda
-- title:
--   OAI.Kadison.MatrixTower.finite_standard_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open OperatorAmplification TracialSequence CyclicColumns HilbertPadding`):
--
--   ```lean
--   theorem finite_standard_bound [TopologicalSpace.SeparableSpace τ.GNS]
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
--       (h : ℕ) (hh : 1 ≤ h)
--       (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
--       (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
--       ‖diagonalAmplification h Y*matrixOperator h X-
--         matrixOperator h X*diagonalAmplification h Y‖ ≤
--         (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` and `OAI.Kadison.OperatorAmplification.SumSpace` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.finiteStandardAlgebra` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.commutatorSeminorm`, `OAI.Kadison.diagonalAmplification` and `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proofs of `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound` and `OAI_Kadison_NormalRepresentation_traced_factor_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C061

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M]

variable (τ : M →ₚ[ℂ] ℂ)

variable (ι : Type) [Fintype ι] [Nonempty ι]

theorem finite_standard_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1 ≤ h)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖ := by
  sorry

end Kadison.MatrixTower

end

end OAI
end
