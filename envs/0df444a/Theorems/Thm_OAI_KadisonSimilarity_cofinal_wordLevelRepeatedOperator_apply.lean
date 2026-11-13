-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_cofinal_wordLevelRepeatedOperator_apply
-- name    : OAI.KadisonSimilarity.cofinal_wordLevelRepeatedOperator_apply
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:04:19.371491+00:00
-- url     : https://prove2.me/theorems/705ba4a0-b53f-4742-9c37-6b5109564bf0
-- title:
--   OAI.KadisonSimilarity.cofinal_wordLevelRepeatedOperator_apply: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.cofinal_wordLevelRepeatedOperator_apply` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/CofinalMatrixTowers.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Tracial/CofinalMatrixTowers.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open Filter`):
--
--   ```lean
--   theorem cofinal_wordLevelRepeatedOperator_apply (n : ℕ) (a : G n) (d : E) (r : F) :
--       Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
--         U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
--           (endpointWord d (fun _ : Fin n => r)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.normalizedPermutationContraction` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.EndpointTensor` and `OAI.KadisonSimilarity.endpointWord` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace` and `OAI.KadisonSimilarity.hilbertTensorInsert` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialMatrixTower` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.WordLevelMatrixActions` and `OAI.KadisonSimilarity.wordLevelRepeatedOperator` (definitions bundle `OAIQ075A033` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Tracial/CofinalMatrixTowers.lean (declaration OAI.KadisonSimilarity.cofinal_wordLevelRepeatedOperator_apply)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Definitions.Def_OAIQ075A033

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

open Filter

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
  (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)
  (hcontraction : ∀ k l b s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
    normalizedPermutationContraction π
      (fun i => T.transition b (b + s) (Nat.le_add_right b s) (v i)) =
      normalizedPermutationContraction π v)

include hleft hunitary hcontraction in
theorem cofinal_wordLevelRepeatedOperator_apply (n : ℕ) (a : G n) (d : E) (r : F) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r))) := by
  sorry

end KadisonSimilarity

end

end OAI
end
