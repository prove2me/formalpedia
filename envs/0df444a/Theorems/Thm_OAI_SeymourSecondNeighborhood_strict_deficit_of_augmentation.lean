-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_strict_deficit_of_augmentation
-- name    : OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:05:58.566362+00:00
-- url     : https://prove2.me/theorems/d39f55ce-55d8-45de-9fb1-a9723a65ce89
-- title:
--   An augmentation step with strict gain gives a strict global deficit
-- statement:
--   Let $E$ be a nonempty finite set and $g$ a function from finite subsets of $E$ to $\mathbb{N}$ with $g(\emptyset)=0$. Suppose that for every proper subset $T\subsetneq E$ there is a nonempty $Q\subseteq E\setminus T$ with
--   $$
--   g(T\cup Q)<g(T)+|Q| .
--   $$
--   Then
--   $$
--   g(E)<|E| .
--   $$
--
--   Each augmentation step gains strictly less than the number of added elements, so the total is strictly below $|E|$. This is the inductive engine for the subset deficit property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/SubsetAugmentation.lean#L11-L56

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample

open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*} [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation (E : Finset V) (hE : E.Nonempty)
    (g : Finset V → ℕ) (hempty : g ∅ = 0)
    (step : ∀ T : Finset V, T ⊆ E → T ≠ E →
      ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ E \ T ∧
        g (T ∪ Q) < g T + Q.card) :
    g E < E.card := by sorry
