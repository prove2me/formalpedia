-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_finite_standard_entrywise_bound
-- name    : OAI.Kadison.MatrixTower.finite_standard_entrywise_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:04:17.473012+00:00
-- url     : https://prove2.me/theorems/9c83d5e5-a001-4324-81d3-f169af0e33e3
-- title:
--   OAI.Kadison.MatrixTower.finite_standard_entrywise_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open OperatorAmplification TracialSequence CyclicColumns HilbertPadding`):
--
--   ```lean
--   theorem finite_standard_entrywise_bound
--       (hE : Monotone (fun n => (E n).hom.range))
--       (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       (X : Matrix κ κ (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
--       (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
--       ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*matrixAction X-
--         matrixAction X*diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤
--         (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixAction X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CyclicColumns.matrixAction` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.MatrixTower.finiteStandardRepresentedDoubledSumDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixGNS.trace` and `OAI.Kadison.MatrixTower.finiteStandardAlgebra` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split); `OAI.Kadison.MatrixTower.generated` (definitions bundle `OAIQ039C071` of this split); `OAI.Kadison.MatrixTower.generated_le` (definitions bundle `OAIQ039C073` of this split); `OAI.Kadison.commutatorSeminorm` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.finite_standard_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
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

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteStandardRepresentedIndexDecidableEq_r8006b4_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardRepresentedColumnDecidableEq_r8006b4_1 : DecidableEq κ := Classical.decEq κ
local instance finiteStandardRepresentedSumDecidableEq_r8006b4_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteStandardRepresentedDoubledSumDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem finite_standard_entrywise_bound
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix κ κ (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*matrixAction X-
      matrixAction X*diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixAction X‖ := by
  sorry

end Kadison.MatrixTower

end

end OAI
end
