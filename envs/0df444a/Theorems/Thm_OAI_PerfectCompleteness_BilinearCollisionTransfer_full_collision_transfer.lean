-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_BilinearCollisionTransfer_full_collision_transfer
-- name    : OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:45:39.115594+00:00
-- url     : https://prove2.me/theorems/5906d39a-9e57-4a6e-b633-fde2a8474123
-- title:
--   OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer` of [lean/OAI/Computability/PerfectCompleteness/Algebra/BilinearWitnessLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Algebra/BilinearWitnessLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.BilinearCollisionTransfer`, with `open scoped BigOperators Classical`, `open UniqueGamesTheorem.Foundations.Games`, `open PerfectCompleteness ProjectionPosterior BilinearWitness`):
--
--   ```lean
--   theorem full_collision_transfer (f : (i : I) → V i →ₗ[𝕜] H)
--       (spans : Function.Surjective (assemble f))
--       (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
--       (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
--       (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
--       (P : (i : I) → FiniteDistribution (Ω i))
--       (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
--       (mean : ∀ i, (P i).expectation (q i) = 1)
--       (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
--       (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
--       (ν : FiniteDistribution ((i : I) → Ω i)) :
--       (forward P q nonnegative mean β hβ hβ').probability
--           (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) -
--         2 * (β * L / (1 - β)) -
--         ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).totalVariation ν ≤
--         ν.probability (fun x => fullCollision (F₀ x) (F₁ x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PerfectCompleteness.BilinearCollisionTransfer.Form`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.fullCollision`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.restrictedCollision`, `OAI.PerfectCompleteness.BilinearWitness.assemble`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution`, `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.expectation` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward` (definitions bundle `OAIQ252P003` of this split); `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.totalVariation` (definitions bundle `OAIQ252P006` of this split); `OAI.PerfectCompleteness.ProjectionPosterior.forward` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Algebra/BilinearWitnessLemmas.lean (declaration OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PerfectCompleteness.BilinearCollisionTransfer

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness ProjectionPosterior BilinearWitness

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem full_collision_transfer (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
    (ν : FiniteDistribution ((i : I) → Ω i)) :
    (forward P q nonnegative mean β hβ hβ').probability
        (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) -
      2 * (β * L / (1 - β)) -
      ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).totalVariation ν ≤
      ν.probability (fun x => fullCollision (F₀ x) (F₁ x)) := by
  sorry

end
end PerfectCompleteness.BilinearCollisionTransfer

end OAI
end
