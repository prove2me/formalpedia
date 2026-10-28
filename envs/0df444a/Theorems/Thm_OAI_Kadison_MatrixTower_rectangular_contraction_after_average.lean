-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_rectangular_contraction_after_average
-- name    : OAI.Kadison.MatrixTower.rectangular_contraction_after_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:04:51.794971+00:00
-- url     : https://prove2.me/theorems/a6e5c1ff-58f6-4432-ad85-9b7d59dee6f6
-- title:
--   OAI.Kadison.MatrixTower.rectangular_contraction_after_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open OperatorAmplification TracialSequence CyclicColumns HilbertPadding`):
--
--   ```lean
--   theorem rectangular_contraction_after_average
--       (hE : Monotone (fun n => (E n).hom.range))
--       (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
--       (X : CStarMatrix κ κ M) (hX : ‖X‖≤1) :
--       ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*
--           matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X-
--         matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X*
--           diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤ 3122*δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CyclicColumns.instDecidableEq_solutions` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.MatrixTower.finiteRectangularContractionDoubledSumDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.CyclicColumns.matrixRepresentation` and `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split); `OAI.Kadison.MatrixTower.generated` (definitions bundle `OAIQ039C071` of this split); `OAI.Kadison.MatrixTower.generated_le` (definitions bundle `OAIQ039C073` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.rectangular_bound_after_average` of this split imports it.
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

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteRectangularContractionIndexDecidableEq_re1630d_1 : DecidableEq ι := Classical.decEq ι
local instance finiteRectangularContractionColumnDecidableEq_re1630d_1 : DecidableEq κ := Classical.decEq κ
local instance finiteRectangularContractionSumDecidableEq_re1630d_1 : DecidableEq (κ⊕ι) := Classical.decEq _
attribute [local instance] OAI.Kadison.MatrixTower.finiteRectangularContractionDoubledSumDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(κ⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) (generated M E))
  (matrixInclusion ((Fin 2)×(κ⊕ι)) (0,Sum.inl k₀) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem rectangular_contraction_after_average
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (X : CStarMatrix κ κ M) (hX : ‖X‖≤1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y*
        matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X-
      matrixRepresentation ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) X*
        diagonal (H:=SumSpace (H:=τ.GNS) ι) κ Y‖ ≤ 3122*δ := by
  sorry

end Kadison.MatrixTower

end

end OAI
end
