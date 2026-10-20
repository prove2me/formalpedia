-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_alphaEdges_isMatching
-- name    : OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_isMatching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:12:23.242711+00:00
-- url     : https://prove2.me/theorems/f2d5d0d4-0c04-4a4a-a8cf-88fb37f421e6
-- title:
--   The left-cover ($\alpha$) edges of an augmented matching form a matching
-- statement:
--   Let $r$ be a relation on a finite set $V$, $R,C\subseteq V\times V$, and $Z=Z(R,C)$ the doubly covered pairs. The augmented bipartite graph has left side $R\sqcup Z$ and right side $C\sqcup Z$. Its edges are: conflicts between $R$ and $C$ (original edges), left covers from $R$ to the right copy of $Z$ ($\alpha$-edges), and right covers from the left copy of $Z$ to $C$ ($\beta$-edges). There are no edges between the two copies of $Z$.
--
--   If $M$ is a matching of the augmented graph, then its $\alpha$-edges, the pairs $(z,a)\in Z\times R$ with $a$ left-covering $z$ and $(a,z)\in M$, form a matching of the left-cover relation:
--   $$
--   \{(z,a):(a,z)\in M\}\ \text{is a matching of }\alpha .
--   $$
--
--   This is used to bound the number of left covers that a pruning can preserve.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean#L117-L131

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

theorem OAI.SeymourSecondNeighborhood.Pruning.alphaEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (AlphaRelation r R C) (alphaEdges M) := by sorry
