-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_originalEdges_isMatching
-- name    : OAI.SeymourSecondNeighborhood.Pruning.originalEdges_isMatching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:11:40.86508+00:00
-- url     : https://prove2.me/theorems/e257ca60-d549-48b0-8871-01244bb1d28f
-- title:
--   The original (conflict) edges of an augmented matching form a matching
-- statement:
--   Let $r$ be a relation on a finite set $V$, $R,C\subseteq V\times V$, and $Z=Z(R,C)$ the doubly covered pairs. The augmented bipartite graph has left side $R\sqcup Z$ and right side $C\sqcup Z$. Its edges are: conflicts between $R$ and $C$ (original edges), left covers from $R$ to the right copy of $Z$ ($\alpha$-edges), and right covers from the left copy of $Z$ to $C$ ($\beta$-edges). There are no edges between the two copies of $Z$.
--
--   If $M$ is a matching of the augmented graph, then its original edges form a matching of the conflict relation between $R$ and $C$:
--   $$
--   \{(a,b)\in R\times C:(a,b)\in M\}\ \text{is a matching}.
--   $$
--
--   Each edge class of an augmented matching can be analysed separately as a matching in its own bipartite graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean#L101-L115

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

theorem OAI.SeymourSecondNeighborhood.Pruning.originalEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (OriginalRelation r R C) (originalEdges M) := by sorry
