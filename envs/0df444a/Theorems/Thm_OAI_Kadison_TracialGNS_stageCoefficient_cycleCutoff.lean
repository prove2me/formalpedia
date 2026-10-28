-- Prove2me | Theorems.Thm_OAI_Kadison_TracialGNS_stageCoefficient_cycleCutoff
-- name    : OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:30:53.72314+00:00
-- url     : https://prove2.me/theorems/ddc5352f-b5d0-4ea9-b784-3e85cb9fb3fb
-- title:
--   OAI.Kadison.TracialGNS.stageCoefficient_cycleCutoff: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialGNS`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open PreHilbert`):
--
--   ```lean
--   theorem stageCoefficient_cycleCutoff (I : ℕ → Type*)
--       [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
--       (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
--       (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
--       (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
--       (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
--       (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
--         Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
--           (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
--       (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
--       ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
--         (∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
--           stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v) ∧
--         ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c σ = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.PreHilbert.wordSpace` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.SchurWeyl.cycleCount` and `OAI.Kadison.SchurWeyl.cycleTrace` (definitions bundle `OAIQ039C029` of this split); `OAI.Kadison.TracialGNS.fullSpace` (definitions bundle `OAIQ039C040` of this split); `OAI.Kadison.TracialGNS.zeroSpace` (definitions bundle `OAIQ039C048` of this split); `OAI.Kadison.TracialGNS.stageCoefficient`, `OAI.Kadison.TracialGNS.wordConjugation` and `OAI.Kadison.TracialGNS.wordLeft` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stageCoefficient_crossing` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C058

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

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include h1 in
theorem stageCoefficient_cycleCutoff (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      (∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
        stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v) ∧
      ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c σ = 0 := by
  sorry

end Kadison.TracialGNS
end

end OAI
end
