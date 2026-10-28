-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_square_symmetry_after_average
-- name    : OAI.Kadison.MatrixTower.square_symmetry_after_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:50.826789+00:00
-- url     : https://prove2.me/theorems/b21b665c-a6d3-44f4-8e8d-e72ddc182834
-- title:
--   OAI.Kadison.MatrixTower.square_symmetry_after_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open OperatorAmplification TracialSequence`):
--
--   ```lean
--   theorem square_symmetry_after_average
--       (hE : Monotone (fun n => (E n).hom.range))
--       (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
--       (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
--         diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
--       (s : unitary (CStarMatrix ι ι M)) (hs0 : MatrixGNS.trace (ι:=ι) τ (s:CStarMatrix ι ι M)=0)
--       (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
--       ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
--         MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y‖ ≤ 3122*δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixGNS.ArraySpace` and `OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.MatrixTower.finiteSquareConditionalBoundDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixGNS.representation` (definitions bundle `OAIQ039C039` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split); `OAI.Kadison.MatrixTower.generated` (definitions bundle `OAIQ039C071` of this split); `OAI.Kadison.MatrixTower.generated_le` (definitions bundle `OAIQ039C073` of this split).
--
--   **Used by.** The proofs of `OAI_Kadison_MatrixTower_finite_standard_matrixOperator_bound` and `OAI.Kadison.MatrixTower.square_contraction_after_average` of this split import it.
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

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

attribute [local instance] OAI.Kadison.MatrixTower.finiteSquareConditionalBoundDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
  (matrixVonNeumann ι i₀ (generated M E))
  (matrixInclusion ι i₀ M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem square_symmetry_after_average
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (s : unitary (CStarMatrix ι ι M)) (hs0 : MatrixGNS.trace (ι:=ι) τ (s:CStarMatrix ι ι M)=0)
    (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
      MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y‖ ≤ 3122*δ := by
  sorry

end MatrixTower

end Kadison

end

end OAI
end
