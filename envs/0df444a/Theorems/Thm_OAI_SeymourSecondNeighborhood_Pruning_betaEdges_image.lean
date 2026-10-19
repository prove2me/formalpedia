-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_betaEdges_image
-- name    : OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:14:01.815367+00:00
-- url     : https://prove2.me/theorems/3e3773d1-4b8f-4826-a401-7233582f444d
-- title:
--   The $\beta$-edges of an augmented matching are exactly its edges out of the left copy of $Z$
-- statement:
--   Let $r$ be a relation on a finite set $V$, $R,C\subseteq V\times V$, and $Z=Z(R,C)$ the doubly covered pairs. The augmented bipartite graph has left side $R\sqcup Z$ and right side $C\sqcup Z$. Its edges are: conflicts between $R$ and $C$ (original edges), left covers from $R$ to the right copy of $Z$ ($\alpha$-edges), and right covers from the left copy of $Z$ to $C$ ($\beta$-edges). There are no edges between the two copies of $Z$.
--
--   If $M$ is a matching of the augmented graph, then lifting its $\beta$-edges recovers exactly the edges of $M$ whose left endpoint lies in the copy of $Z$:
--   $$
--   \mathrm{lift}\bigl(\beta\text{-edges of }M\bigr)=\{e\in M:\ \text{left end of }e\in Z\}.
--   $$
--
--   Together with the corresponding statement for $\alpha$-edges, this partitions an augmented matching by edge type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/AugmentedGraph.lean#L194-L212

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

theorem OAI.SeymourSecondNeighborhood.Pruning.betaEdges_image
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    (betaEdges M).image betaLift = M.filter (fun e => e.1.isRight) := by sorry
