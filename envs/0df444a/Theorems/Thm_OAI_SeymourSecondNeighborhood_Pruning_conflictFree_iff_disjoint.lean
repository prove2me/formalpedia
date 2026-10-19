-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_conflictFree_iff_disjoint
-- name    : OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:08:13.83133+00:00
-- url     : https://prove2.me/theorems/ea734c8b-f68a-4243-99e4-e09aa2adc6ec
-- title:
--   Conflict-freeness is disjointness of the left and right images
-- statement:
--   Let $r$ be a relation on a finite set $V$ and let $P,Q\subseteq V\times V$ be sets of pairs. $(P,Q)$ is compatible (conflict-free) if there are no $a\in P$, $b\in Q$ with $a_1\to b_1$ and $b_2\to a_2$. The left image of $P$ is $\{z:\exists p,\ (p,z_2)\in P,\ p\to z_1\}$, and the right image of $Q$ is $\{z:\exists s,\ (z_1,s)\in Q,\ s\to z_2\}$. Then
--   $$
--   (P,Q)\ \text{is conflict-free}\iff\mathrm{left}(P)\cap\mathrm{right}(Q)=\emptyset .
--   $$
--
--   A conflict between $a\in P$ and $b\in Q$ is the same as a pair $z=(b_1,a_2)$ that is covered from both sides. This lets conflicts be counted through covered pairs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/PruningDefinitions.lean#L171-L185

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint {r : V → V → Prop} {R C : Finset (V × V)} :
    ConflictFree r R C ↔ Disjoint (leftImage r R) (rightImage r C) := by sorry
