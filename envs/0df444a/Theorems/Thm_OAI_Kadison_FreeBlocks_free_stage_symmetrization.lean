-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_free_stage_symmetrization
-- name    : OAI.Kadison.FreeBlocks.free_stage_symmetrization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:35:51.610729+00:00
-- url     : https://prove2.me/theorems/71d66560-464b-4b00-b33c-f9e08d7cfaf5
-- title:
--   OAI.Kadison.FreeBlocks.free_stage_symmetrization: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace MeasureTheory`, `open scoped ComplexOrder InnerProductSpace`, `open FreeMoments FreeWordTensor FreeWordAction`):
--
--   ```lean
--   theorem free_stage_symmetrization (G : t.functional.GNS →L[ℂ] t.functional.GNS)
--       (ε : ℝ) (hε : 0≤ε) (β : ℂ) (s : A) (hs : s∈S true)
--       (hGD : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
--       (hC : ∀ x, CornerSymmetrization.CornerElement
--         (factorOperators t f) (ambientOperators t S)
--         (TracialGNS.vacuum t.functional) β x → ‖G*x-x*G‖≤ε*‖x‖) :
--       ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
--         ‖V‖≤‖G‖ ∧
--         (∀ n u, V*(innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
--           t.functional.GNS →L[ℂ] t.functional.GNS)=
--           (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
--             t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
--         (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
--         (∀ x, CornerSymmetrization.CornerElement
--           (factorOperators t f) (ambientOperators t S)
--           (TracialGNS.vacuum t.functional) β x → ‖V*x-x*V‖≤ε*‖x‖) ∧
--         (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
--           (baseEmbedding t S hfree).toContinuousLinearMap).comp
--           ((V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V).comp
--             (baseEmbedding t S hfree).toContinuousLinearMap)=
--         (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
--           (baseEmbedding t S hfree).toContinuousLinearMap).comp
--           ((G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G).comp
--             (baseEmbedding t S hfree).toContinuousLinearMap)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CornerSymmetrization.CornerElement` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.ambientOperators`, `OAI.Kadison.FreeBlocks.baseEmbedding` and `OAI.Kadison.FreeBlocks.factorOperators` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace MeasureTheory

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))
  (S : Bool → StarSubalgebra ℂ A) (f : D →⋆ₐ[ℂ] A) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a, φ m (inc h a)=φ n a)

omit [PartialOrder D] [StarOrderedRing D] [∀ n, Nonempty (I n)] in
include hinc in
theorem free_stage_symmetrization (G : t.functional.GNS →L[ℂ] t.functional.GNS)
    (ε : ℝ) (hε : 0≤ε) (β : ℂ) (s : A) (hs : s∈S true)
    (hGD : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (hC : ∀ x, CornerSymmetrization.CornerElement
      (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) β x → ‖G*x-x*G‖≤ε*‖x‖) :
    ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
      ‖V‖≤‖G‖ ∧
      (∀ n u, V*(innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
        t.functional.GNS →L[ℂ] t.functional.GNS)=
        (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
          t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
      (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
      (∀ x, CornerSymmetrization.CornerElement
        (factorOperators t f) (ambientOperators t S)
        (TracialGNS.vacuum t.functional) β x → ‖V*x-x*V‖≤ε*‖x‖) ∧
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
        (baseEmbedding t S hfree).toContinuousLinearMap).comp
        ((V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V).comp
          (baseEmbedding t S hfree).toContinuousLinearMap)=
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
        (baseEmbedding t S hfree).toContinuousLinearMap).comp
        ((G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G).comp
          (baseEmbedding t S hfree).toContinuousLinearMap) := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
