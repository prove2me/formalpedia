-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_pruning_of_augmented_cover
-- name    : OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:37:13.799476+00:00
-- url     : https://prove2.me/theorems/d466a391-b238-4210-8e84-83aaaec9b0c7
-- title:
--   A small vertex cover of the augmented graph without isolated vertices yields a pruning
-- statement:
--   Let $r$ be a relation on a finite set $X$, read as a digraph with arcs $x\to y$, and let $R,C\subseteq X\times X$. A pair $\rho\in R$ left-covers $z$ if $\rho_2=z_2$ and $\rho_1\to z_1$. A pair $\gamma\in C$ right-covers $z$ if $\gamma_1=z_1$ and $\gamma_2\to z_2$. $Z=Z(R,C)$ is the set of pairs that are left-covered by $R$ and right-covered by $C$. $\rho\in R$ and $\gamma\in C$ conflict if $\rho_1\to\gamma_1$ and $\gamma_2\to\rho_2$. $H=H(R,C)$ is the set of hub pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$. The augmented bipartite graph has left side $R\sqcup Z$ and right side $C\sqcup Z$, with conflict edges $R\to C$, left-cover edges from $R$ to the right copy of $Z$, and right-cover edges from the left copy of $Z$ to $C$.
--
--   Let $(A,B)$ be a vertex cover of the augmented graph, with $A\subseteq R\sqcup Z$ and $B\subseteq C\sqcup Z$, in which every vertex has at least one augmented edge. Assume
--   $$
--   |A|+|B|\le|H|+|Z| .
--   $$
--   Then $(R,C)$ has a pruning $(R',C')$: $R'\subseteq R$, $C'\subseteq C$, $(R',C')$ is conflict-free, every element of $R$ or $C$ in no conflict is kept, and
--   $$
--   |R\setminus R'|+|C\setminus C'|\le|H|+|\{z\in Z:z\text{ not covered by }(R',C')\}| .
--   $$
--
--   The cover vertices in $R$ and $C$ are deleted. Its vertices in the copies of $Z$ pay for the pairs of $Z$ that stay covered.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/CoverPruning.lean#L13-L126

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_of_augmented_cover
    (r : V → V → Prop) (R C : Finset (V × V))
    (A : Finset (LeftVertex r R C)) (B : Finset (RightVertex r R C))
    (hcover : IsVertexCover (AugmentedEdge r R C) A B)
    (hA : ∀ a ∈ A, ∃ b, AugmentedEdge r R C a b)
    (hB : ∀ b ∈ B, ∃ a, AugmentedEdge r R C a b)
    (hbound : A.card + B.card ≤ (H r R C).card + (Z r R C).card) :
    ∃ R' C', PruningResult r R C R' C' := by sorry
