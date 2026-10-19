-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_isMaximumMatching_rightBlock_of_minimum_crossing
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:17:57.716496+00:00
-- url     : https://prove2.me/theorems/da9cdc7f-9e69-45d0-b3e5-8668ee2a846d
-- title:
--   A maximum matching with fewest crossing edges is maximum on the right block
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation between finite sets. A matching is a set of edges no two of which share an endpoint. It is maximum if no matching is larger. A vertex cover is a pair $A\subseteq L$, $B\subseteq R$ meeting every edge. Let $P\subseteq L$ and $Q\subseteq R$ be such that every edge into $Q$ starts in $P$: $E(a,b)$ and $b\in Q$ imply $a\in P$. Let $M$ be a maximum matching that minimizes, among all maximum matchings, the number of crossing edges $(a,b)$ with $a\in P$ and $b\notin Q$. Then
--   $$
--   \{(a,b)\in M:\ b\in Q\}
--   $$
--   is a maximum matching of the subgraph $E\cap(L\times Q)$.
--
--   Under this block structure, a suitably extremal global maximum matching restricts to maximum matchings of the block. Block ranks can then be read off one global matching.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean#L18-L160

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

theorem OAI.SeymourSecondNeighborhood.Bipartite.isMaximumMatching_rightBlock_of_minimum_crossing
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a)
    {M : Finset (L × R)} (hM : IsMaximumMatching E M)
    (hmin : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card) :
    IsMaximumMatching (fun a b => E a b ∧ Q b)
      (M.filter (fun e => Q e.2)) := by sorry
