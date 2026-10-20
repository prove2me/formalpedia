-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_original_add_auxiliary_card_le_corners
-- name    : OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:35:54.265057+00:00
-- url     : https://prove2.me/theorems/9d70b13a-3344-4b17-a908-40365b704435
-- title:
--   Conflicts disjoint from maximum cover matchings are bounded by $|Z|+|H|-|\alpha|-|\beta|$
-- statement:
--   Let $r$ be a relation on a finite set $X$, read as a digraph with arcs $x\to y$, and let $R,C\subseteq X\times X$. A pair $\rho\in R$ left-covers $z$ if $\rho_2=z_2$ and $\rho_1\to z_1$. A pair $\gamma\in C$ right-covers $z$ if $\gamma_1=z_1$ and $\gamma_2\to z_2$. $Z=Z(R,C)$ is the set of pairs that are left-covered by $R$ and right-covered by $C$. $\rho\in R$ and $\gamma\in C$ conflict if $\rho_1\to\gamma_1$ and $\gamma_2\to\rho_2$. $H=H(R,C)$ is the set of hub pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$.
--
--   Let $\alpha\subseteq Z\times R$ be a maximum matching of the left-cover relation and $\beta\subseteq Z\times C$ a maximum matching of the right-cover relation. Let $E$ be a finite set with injective maps $\mathrm{left}:E\to R$ and $\mathrm{right}:E\to C$ such that
--   - $\mathrm{left}(e)$ and $\mathrm{right}(e)$ conflict for every $e$;
--   - no $\mathrm{left}(e)$ is the $R$-endpoint of an edge of $\alpha$;
--   - no $\mathrm{right}(e)$ is the $C$-endpoint of an edge of $\beta$.
--
--   Then
--   $$
--   |E|+|\alpha|+|\beta|\le|Z|+|H| .
--   $$
--
--   In the augmented graph this bounds any matching whose cover parts are maximum. It is the combinatorial inequality behind the pruning lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/RankBoundFromMinors.lean#L13-L42

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
open scoped Matrix
variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]

theorem OAI.SeymourSecondNeighborhood.Pruning.original_add_auxiliary_card_le_corners
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : Bipartite.IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : Bipartite.IsMaximumMatching (matrixNTransposeSupport r R C) β)
    (left : E → ↥R) (right : E → ↥C)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleft_disjoint : ∀ e (f : ↥α), left e ≠ f.1.2)
    (hright_disjoint : ∀ e (f : ↥β), right e ≠ f.1.2)
    (hconflict : ∀ e, Conflict r (left e).1 (right e).1) :
    Fintype.card E + α.card + β.card ≤ (Z r R C).card + (H r R C).card := by sorry
