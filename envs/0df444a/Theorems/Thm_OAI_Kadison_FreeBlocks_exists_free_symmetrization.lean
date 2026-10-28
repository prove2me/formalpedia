-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_exists_free_symmetrization
-- name    : OAI.Kadison.FreeBlocks.exists_free_symmetrization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:35:04.025994+00:00
-- url     : https://prove2.me/theorems/20d086e7-e8ae-4a92-98d0-5a8fc2cb186e
-- title:
--   OAI.Kadison.FreeBlocks.exists_free_symmetrization: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator`, `open MeasureTheory MeasureTheory.Measure`, `open FreeWordTensor FreeMoments FreeWordAction`):
--
--   ```lean
--   theorem exists_free_symmetrization : ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
--       ‖V‖≤‖G‖ ∧
--       (∀ n u, V*(innerRepresentation t ht f S i hS hfree hgen
--           (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)=
--         (innerRepresentation t ht f S i hS hfree hgen
--           (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
--       (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
--       (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
--         (TracialGNS.vacuum t.functional) r x → ‖V*x-x*V‖≤ε*‖x‖) ∧
--       (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
--         (TracialGNS.vacuum t.functional) r x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
--       (baseSpace t S j).starProjection*(V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V)*
--         (baseSpace t S j).starProjection=
--       (baseSpace t S j).starProjection*(G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G)*
--         (baseSpace t S j).starProjection
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.instIsClosedCoeSubmoduleComplexCyclicSubspace` and `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CornerSymmetrization.CornerElement` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.ambientOperators`, `OAI.Kadison.FreeBlocks.baseSpace` and `OAI.Kadison.FreeBlocks.factorOperators` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_stage_symmetrization` of this split imports it.
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

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)

variable (ε : ℝ) (hε : 0≤ε) (r : ℂ)

variable (hC : ∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
    (TracialGNS.vacuum t.functional) r x → ‖G*x-x*G‖≤ε*‖x‖)

variable (s : A) (hs : s∈S j) (hji : j≠i)

omit [PartialOrder D] [StarOrderedRing D] in
include he hGL hε hC hs hji in
theorem exists_free_symmetrization : ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
    ‖V‖≤‖G‖ ∧
    (∀ n u, V*(innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)=
      (innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
    (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V*x-x*V‖≤ε*‖x‖) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
    (baseSpace t S j).starProjection*(V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V)*
      (baseSpace t S j).starProjection=
    (baseSpace t S j).starProjection*(G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G)*
      (baseSpace t S j).starProjection := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
