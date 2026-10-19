-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_augmented_matching_card
-- name    : OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:16:00.209728+00:00
-- url     : https://prove2.me/theorems/dac314a8-c699-4794-b9be-485f3c06e6a5
-- title:
--   An augmented matching splits into its original, $\alpha$- and $\beta$-edges
-- statement:
--   Let $r$ be a relation on a finite set $V$, $R,C\subseteq V\times V$, and $Z$ the doubly covered pairs. The augmented bipartite graph has left side $R\sqcup Z$ and right side $C\sqcup Z$. Its edges are conflicts between $R$ and $C$ (original edges), left covers from $R$ into the copy of $Z$ ($\alpha$-edges), and right covers from the copy of $Z$ into $C$ ($\beta$-edges).
--
--   For every matching $M$ of the augmented graph,
--   $$
--   |M|=|\text{original edges of }M|+|\alpha\text{-edges of }M|+|\beta\text{-edges of }M| .
--   $$
--
--   Matchings of the augmented graph can thus be counted by type. This lets matching sizes be compared with sizes of conflict sets and cover sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean#L249-L287

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : V → V → Prop} {R C : Finset (V × V)}

theorem OAI.SeymourSecondNeighborhood.Pruning.augmented_matching_card
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    M.card = (originalEdges M).card + (alphaEdges M).card + (betaEdges M).card := by sorry
