-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_vertexCover_card_eq_of_isMaximumMatching
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:26:27.350583+00:00
-- url     : https://prove2.me/theorems/1bef7280-5965-4c43-9713-7aa9b55e0f26
-- title:
--   A maximum matching has a vertex cover of equal size consisting of non-isolated vertices
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation between finite sets. A matching is a set of edges no two of which share an endpoint. It is maximum if no matching is larger. A vertex cover is a pair $A\subseteq L$, $B\subseteq R$ meeting every edge. If $M$ is a maximum matching, then there is a vertex cover $(A,B)$ such that
--   $$
--   |A|+|B|=|M|,
--   $$
--   and every vertex of $A$ and of $B$ has at least one edge.
--
--   Maximum matchings and minimum vertex covers have the same size. The cover can moreover be taken without isolated vertices, which is convenient when the cover indexes rows and columns of a matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingCover.lean#L181-L222

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {E : L → R → Prop}

theorem OAI.SeymourSecondNeighborhood.Bipartite.exists_vertexCover_card_eq_of_isMaximumMatching {M : Finset (L × R)}
    (hM : IsMaximumMatching E M) :
    ∃ A : Finset L, ∃ B : Finset R,
      IsVertexCover E A B ∧ A.card + B.card = M.card ∧
      (∀ l ∈ A, ∃ r, E l r) ∧ (∀ r ∈ B, ∃ l, E l r) := by sorry
