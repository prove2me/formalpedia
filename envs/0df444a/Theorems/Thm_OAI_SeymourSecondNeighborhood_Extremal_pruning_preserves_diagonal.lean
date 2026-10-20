-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Extremal_pruning_preserves_diagonal
-- name    : OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:38:06.581742+00:00
-- url     : https://prove2.me/theorems/c3041ea5-5a51-4736-b8f6-7d6066017447
-- title:
--   Pruning the candidate sets of an admissible pair gives an admissible pair
-- statement:
--   Let $r$ be a relation on a finite set $V$ and $P,Q\subseteq V\times V$. $(P,Q)$ is admissible if no $a\in P$ and $b\in Q$ satisfy $a_1\to b_1$ and $b_2\to a_2$, and both $P$ and $Q$ contain the diagonal $\Delta=\{(v,v)\}$. The left image of $P$ is $\{z:\exists p,\ (p,z_2)\in P,\ p\to z_1\}$ and the right image of $Q$ is $\{z:\exists s,\ (z_1,s)\in Q,\ s\to z_2\}$. The left candidates of $Q$ are the pairs outside the right image of the right image of $Q$. The right candidates of $P$ are the pairs outside the left image of the left image of $P$.
--
--   If $(P,Q)$ is admissible and $(P',Q')$ is a pruning of (left candidates of $Q$, right candidates of $P$), then
--   $$
--   (P',Q')\ \text{is admissible.}
--   $$
--
--   The pruning removes all conflicts, so only the diagonal needs to be checked. This lets the extremal argument stay within admissible pairs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCompatibility.lean#L188-L202

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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Extremal
open Pruning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.Extremal.pruning_preserves_diagonal {r : V → V → Prop}
    {P Q P' Q' : Finset (V × V)} (h : Admissible r P Q)
    (hp : PruningResult r (leftCandidate r Q) (rightCandidate r P) P' Q') :
    Admissible r P' Q' := by sorry
