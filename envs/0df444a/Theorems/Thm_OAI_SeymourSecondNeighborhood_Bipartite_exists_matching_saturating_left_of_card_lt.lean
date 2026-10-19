-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_matching_saturating_left_of_card_lt
-- name    : OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:17:25.5431+00:00
-- url     : https://prove2.me/theorems/5b331109-3523-4685-9069-74155a32df22
-- title:
--   A smaller matching's left vertices can be covered by a matching of the larger size
-- statement:
--   Let $E\subseteq L\times R$ be a bipartite relation between finite sets. A matching is a set of edges no two of which share an endpoint. It is maximum if no matching is larger. A vertex cover is a pair $A\subseteq L$, $B\subseteq R$ meeting every edge.
--
--   If $M$ and $N$ are matchings with $|M|<|N|$, then there is a matching $Q$ with $|Q|=|N|$ whose set of left endpoints contains all left endpoints of $M$:
--   $$
--   \pi_L(M)\subseteq\pi_L(Q) .
--   $$
--
--   This exchange property, a matroid-type augmentation for the left endpoints of matchings, lets one assume that a larger matching extends the left side of a given one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingExchange.lean#L43-L113

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite
variable {L R : Type*} {E : L → R → Prop}

theorem OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {M N : Finset (L × R)} (hM : IsMatching E M) (hN : IsMatching E N)
    (hcard : M.card < N.card) :
    ∃ Q : Finset (L × R), IsMatching E Q ∧ Q.card = N.card ∧
      M.image Prod.fst ⊆ Q.image Prod.fst := by sorry
