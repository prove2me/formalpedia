-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_minimum_cover_has_equal_matching
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:25:56.226145+00:00
-- url     : https://prove2.me/theorems/d824448d-6d50-41a4-8828-fa27ac901a57
-- title:
--   König's theorem: a minimum vertex cover has a matching of the same size
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation between finite sets. A matching is a set of edges no two of which share an endpoint. It is maximum if no matching is larger. A vertex cover is a pair $A\subseteq L$, $B\subseteq R$ meeting every edge. If $(A,B)$ is a vertex cover of minimum size, then there is a matching $N$ with
--   $$
--   |N|=|A|+|B| .
--   $$
--
--   Combined with the inequality $|M|\le|A|+|B|$ for every matching and every cover, this is König's theorem: maximum matching size equals minimum vertex cover size.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingCover.lean#L75-L179

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

theorem OAI.SeymourSecondNeighborhood.Bipartite.minimum_cover_has_equal_matching {A : Finset L} {B : Finset R}
    (hC : IsVertexCover E A B)
    (hmin : ∀ A' B', IsVertexCover E A' B' →
      A.card + B.card ≤ A'.card + B'.card) :
    ∃ N : Finset (L × R), IsMatching E N ∧ N.card = A.card + B.card := by sorry
