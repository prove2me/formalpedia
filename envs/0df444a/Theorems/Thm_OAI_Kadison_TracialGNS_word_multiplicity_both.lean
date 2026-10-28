-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_word_multiplicity_both
-- name    : OAI.Kadison.TracialGNS.word_multiplicity_both
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:40.569171+00:00
-- url     : https://prove2.me/theorems/912802e2-9fe2-4698-96b2-d10a944ed35e
-- title:
--   OAI.Kadison.TracialGNS.word_multiplicity_both: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert HilbertTensor`):
--
--   ```lean
--   theorem word_multiplicity_both {k : ℕ} {J : Type*}
--       [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
--       (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
--         Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J))
--       (hclass : ∀ a b : J, ∃ c : Equiv.Perm (Fin k) → ℂ,
--         scalarSlice T a b = ∑ σ, c σ •
--           (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap)
--       (z : zeroSpace τ) (hz : ‖z‖ = 1) :
--       ∃ B : J →L[ℂ] J, ‖B‖ ≤ ‖T‖ ∧
--         (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
--           T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
--             pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B a)) ∧
--         (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
--           T.adjoint (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
--             pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B.adjoint a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power`, `OAI.Kadison.PreHilbert.word` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertTensor.pair` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.centeredSpace` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.HilbertTensor.scalarSlice` (definitions bundle `OAIQ039C027` of this split); `OAI.Kadison.PreHilbert.wordReindex` and `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.actual_word_structure` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C040
import Definitions.Def_OAIQ039C048

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

include h1 in
theorem word_multiplicity_both {k : ℕ} {J : Type*}
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J))
    (hclass : ∀ a b : J, ∃ c : Equiv.Perm (Fin k) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap)
    (z : zeroSpace τ) (hz : ‖z‖ = 1) :
    ∃ B : J →L[ℂ] J, ‖B‖ ≤ ‖T‖ ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B a)) ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T.adjoint (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B.adjoint a)) := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
