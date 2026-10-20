-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_maximum_matching_with_maximum_blocks
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:19:25.514987+00:00
-- url     : https://prove2.me/theorems/055ebbe5-6316-46ef-9302-16411e375b58
-- title:
--   A single maximum matching that is simultaneously maximum on two blocks
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation between finite sets. A matching is a set of edges no two of which share an endpoint. It is maximum if no matching is larger. A vertex cover is a pair $A\subseteq L$, $B\subseteq R$ meeting every edge. Let $P\subseteq L$ and $Q\subseteq R$ with every edge into $Q$ starting in $P$. Then there is a maximum matching $M$ of $E$ such that
--   $$
--   M\cap(L\times Q)\ \text{is maximum in }E\cap(L\times Q),\qquad M\cap\bigl((L\setminus P)\times R\bigr)\ \text{is maximum in }E\cap\bigl((L\setminus P)\times R\bigr).
--   $$
--
--   One global maximum matching realizes the maximum matching sizes of both blocks at once. This is needed when ranks of a block-structured matrix and of its two diagonal blocks are compared.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean#L246-L264

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite
variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {E : L → R → Prop}

theorem OAI.SeymourSecondNeighborhood.Bipartite.exists_maximum_matching_with_maximum_blocks
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a) :
    ∃ M : Finset (L × R), IsMaximumMatching E M ∧
      IsMaximumMatching (fun a b => E a b ∧ Q b)
        (M.filter (fun e => Q e.2)) ∧
      IsMaximumMatching (fun a b => E a b ∧ ¬P a)
        (M.filter (fun e => ¬P e.1)) := by sorry
