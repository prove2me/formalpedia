-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_exists_matrix_freeCornerPosition
-- name    : OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:42.192749+00:00
-- url     : https://prove2.me/theorems/f3c2aebd-fc6d-4fce-ac1f-a56540cbe53f
-- title:
--   OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped Topology ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open OperatorAmplification TracialSequence`):
--
--   ```lean
--   theorem exists_matrix_freeCornerPosition [TopologicalSpace.SeparableSpace τ.GNS]
--       (hE : Monotone (fun n => (E n).hom.range))
--       (hsize : ∀ n,n+1 ≤ Fintype.card (E n).I)
--       (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (hω : (ω : Filter ℕ) ≤ atTop) :
--       Nonempty (FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
--         (matrixVonNeumann ι i₀ (generated M E))
--         (matrixInclusion ι i₀ M (generated M E) (generated_le M E)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` and `OAI.Kadison.OperatorAmplification.SumSpace` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixTower.matrixFreePositionProducerDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split); `OAI.Kadison.MatrixTower.generated` (definitions bundle `OAIQ039C071` of this split); `OAI.Kadison.MatrixTower.generated_le` (definitions bundle `OAIQ039C073` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.finite_standard_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073

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

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H) [Nontrivial M]

attribute [local instance] OAI.Kadison.MatrixTower.matrixFreePositionProducerDecidableEq
variable (E : ℕ → Stage M) (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

theorem exists_matrix_freeCornerPosition [TopologicalSpace.SeparableSpace τ.GNS]
    (hE : Monotone (fun n => (E n).hom.range))
    (hsize : ∀ n,n+1 ≤ Fintype.card (E n).I)
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (hω : (ω : Filter ℕ) ≤ atTop) :
    Nonempty (FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
      (matrixVonNeumann ι i₀ (generated M E))
      (matrixInclusion ι i₀ M (generated M E) (generated_le M E))) := by
  sorry

end Kadison.MatrixTower

end

end
end

end OAI
end
