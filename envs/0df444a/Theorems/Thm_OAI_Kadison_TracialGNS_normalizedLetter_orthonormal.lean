-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_normalizedLetter_orthonormal
-- name    : OAI.Kadison.TracialGNS.normalizedLetter_orthonormal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:10.581628+00:00
-- url     : https://prove2.me/theorems/0fdfb8e7-39e2-4b51-9d1a-3fb395348b53
-- title:
--   OAI.Kadison.TracialGNS.normalizedLetter_orthonormal: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open MatrixAlphabet`):
--
--   ```lean
--   lemma normalizedLetter_orthonormal {J : Type*} (o : I) (b : J ↪ I)
--       (hb : ∀ j, b j ≠ o) :
--       Orthonormal ℂ (fun j => centeredStageVector τ φ (normalizedLetter o (b j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixAlphabet.normalizedLetter` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.centeredSpace` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.TracialGNS.centeredStageVector` (definitions bundle `OAIQ039C052` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.TracialGNS.actual_word_structure` and `OAI.Kadison.TracialGNS.stage_pairing_same_side_zero` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C052

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

open MatrixAlphabet

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

include hτ h1 in
lemma normalizedLetter_orthonormal {J : Type*} (o : I) (b : J ↪ I)
    (hb : ∀ j, b j ≠ o) :
    Orthonormal ℂ (fun j => centeredStageVector τ φ (normalizedLetter o (b j))) := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
