-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_eval_maximal_support_rank
-- name    : OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:28:04.697523+00:00
-- url     : https://prove2.me/theorems/0b39560d-5d71-4b51-987b-b714556f1961
-- title:
--   A common real point where finitely many supported variable matrices attain maximal rank
-- statement:
--   Let $K$ be an infinite field and $\kappa$ a finite index set. For each $k\in\kappa$ let $I_k,J_k$ be finite, with a support relation on $I_k\times J_k$ and a labelling of support positions by variables, injective on each support. Let $M_k$ be the corresponding supported variable matrix over $K[X_s]$. Let $(f_t)_{t\in\tau}$ be a finite family of nonzero polynomials. Then there is a point $a\in K^\sigma$ such that $f_t(a)\ne0$ for all $t$, and for every $k$ and every matrix $D\in K^{I_k\times J_k}$ vanishing off the $k$-th support,
--   $$
--   \operatorname{rank}D\le\operatorname{rank}M_k(a).
--   $$
--
--   A single generic choice of coefficients makes every supported matrix attain the maximal rank allowed by its zero pattern, while avoiding finitely many prescribed bad sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankFamily.lean#L45-L93

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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank

open OAI OAI.SeymourSecondNeighborhood
open Bipartite
variable {σ κ τ K : Type*} [Field K] [Infinite K] [Fintype κ] [Fintype τ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

theorem OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank
    (support : ∀ k, I k → J k → Prop) (label : ∀ k, I k → J k → σ)
    (hlabel : ∀ k i j i' j', support k i j → support k i' j' →
      label k i j = label k i' j' → i = i' ∧ j = j')
    (extra : τ → MvPolynomial σ K) (hextra : ∀ t, extra t ≠ 0) :
    ∃ a : σ → K, (∀ t, MvPolynomial.eval a (extra t) ≠ 0) ∧
      ∀ k (D : Matrix (I k) (J k) K),
        (∀ i j, ¬ support k i j → D i j = 0) →
        D.rank ≤ (evalPolynomialMatrix a
          (supportedVariableMatrix (R := K) (support k) (label k))).rank := by sorry
