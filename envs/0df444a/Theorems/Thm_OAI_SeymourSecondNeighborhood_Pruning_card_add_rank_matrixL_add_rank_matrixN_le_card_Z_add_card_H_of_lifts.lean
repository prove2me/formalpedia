-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
-- name    : OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:34:41.360202+00:00
-- url     : https://prove2.me/theorems/80fc4389-4d54-44d2-994f-9e0c063bcc04
-- title:
--   Kernel lifts and the ranks of $L$ and $N$ are bounded by $|Z|+|H|$
-- statement:
--   Let $r$ be a relation on a finite set $X$, read as a digraph with arcs $x\to y$, and let $R,C\subseteq X\times X$. A pair $\rho\in R$ left-covers $z$ if $\rho_2=z_2$ and $\rho_1\to z_1$. A pair $\gamma\in C$ right-covers $z$ if $\gamma_1=z_1$ and $\gamma_2\to z_2$. $Z=Z(R,C)$ is the set of pairs that are left-covered by $R$ and right-covered by $C$. $\rho\in R$ and $\gamma\in C$ conflict if $\rho_1\to\gamma_1$ and $\gamma_2\to\rho_2$. $H=H(R,C)$ is the set of hub pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$. For coefficient functions $a,b:X\times X\to\mathbb{R}$ supported on arcs ($a(x,y)=b(x,y)=0$ unless $x\to y$), the cover matrices are $L\in\mathbb{R}^{Z\times R}$ with $L_{z,\rho}=a(\rho_1,z_1)$ if $z_2=\rho_2$ and $0$ otherwise, and $N\in\mathbb{R}^{C\times Z}$ with $N_{\gamma,z}=b(\gamma_2,z_2)$ if $\gamma_1=z_1$ and $0$ otherwise. The hub matrices are $B\in\mathbb{R}^{H\times R}$ with $B_{h,\rho}=b(h_2,\rho_2)$ if $h_1=\rho_1$, and $A\in\mathbb{R}^{C\times H}$ with $A_{\gamma,h}=a(h_1,\gamma_1)$ if $\gamma_2=h_2$ (and $0$ otherwise). Assume $b$ has locally maximal ranks. Let $E$ be a finite index set with maps $\mathrm{left}:E\to R$ and $\mathrm{right}:E\to C$ such that $\mathrm{left}(e)$ and $\mathrm{right}(e)$ conflict for every $e$. Let $U_e\in\mathbb{R}^R$ and $W_e\in\mathbb{R}^C$ satisfy
--   - $LU_e=0$ and $N^{\mathsf T}W_e=0$;
--   - $W_e(\mathrm{right}(e))=1$;
--   - $U_e(\mathrm{left}(f))=1$ if $e=f$ and $0$ otherwise.
--
--   Then
--   $$
--   |E|+\operatorname{rank}L+\operatorname{rank}N\le|Z|+|H| .
--   $$
--
--   This combines the hub bound for $NL$ with Sylvester's rank inequality through the inner dimension $Z$. It is the linear-algebra form of the bound on augmented matchings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/CompositeRankBound.lean#L60-L88

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
open Matrix
open scoped Classical
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E + (matrixL r R C a).rank + (matrixN r R C b).rank ≤
      (Z r R C).card + (H r R C).card := by sorry
