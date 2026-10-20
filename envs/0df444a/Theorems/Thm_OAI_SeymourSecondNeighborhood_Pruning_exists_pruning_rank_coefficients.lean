-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_exists_pruning_rank_coefficients
-- name    : OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:33:22.938524+00:00
-- url     : https://prove2.me/theorems/b1cef98f-8575-42df-9632-aad676c66312
-- title:
--   Generic coefficients realise the maximum matching sizes as ranks of the cover matrices
-- statement:
--   Let $r$ be a relation on a finite set $X$, read as a digraph with arcs $x\to y$, and let $R,C\subseteq X\times X$. A pair $\rho\in R$ left-covers $z$ if $\rho_2=z_2$ and $\rho_1\to z_1$. A pair $\gamma\in C$ right-covers $z$ if $\gamma_1=z_1$ and $\gamma_2\to z_2$. $Z=Z(R,C)$ is the set of pairs that are left-covered by $R$ and right-covered by $C$. $\rho\in R$ and $\gamma\in C$ conflict if $\rho_1\to\gamma_1$ and $\gamma_2\to\rho_2$. $H=H(R,C)$ is the set of hub pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$. The coefficient variables are two copies of $X\times X$. For a real assignment $v$ of the variables, the selected coefficients $a_v(x,y)$ and $b_v(x,y)$ equal the value of the corresponding variable of the first, respectively second, copy when $x\to y$, and $0$ otherwise. The coefficients $b$ have locally maximal ranks if for every arc $p\to i$, the local matrix $D^{(p,i)}_b=(b(s,j))_{s\in C_i,\,j\in R_p}$, with $C_i=\{s:(i,s)\in C\}$ and $R_p=\{j:(p,j)\in R\}$, has the largest rank among all real matrices on $C_i\times R_p$ vanishing outside the positions $(s,j)$ with $s\to j$.
--
--   Let $\alpha$ be a maximum matching of the left-cover relation on $Z\times R$ and $\beta$ a maximum matching of the right-cover relation on $Z\times C$. Then there is an assignment $v$ such that $a_v,b_v$ are supported on arcs, $b_v$ has locally maximal ranks, and the cover matrices $L,N$ built from $a_v,b_v$ satisfy:
--   - the minor of $L$ on the rows and columns matched by $\alpha$ is nonsingular;
--   - the minor of $N^{\mathsf T}$ on the rows and columns matched by $\beta$ is nonsingular;
--   - the ranks equal the matching numbers:
--   $$
--   \operatorname{rank}L=|\alpha|,\qquad\operatorname{rank}N^{\mathsf T}=|\beta| .
--   $$
--
--   All rank information needed later is thus realised by one choice of coefficients.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankSelection.lean#L35-L75

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Bipartite
open scoped Matrix
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.SeymourSecondNeighborhood.Pruning.exists_pruning_rank_coefficients
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : IsMaximumMatching (matrixNTransposeSupport r R C) β) :
    ∃ v : CoefficientVariables X → ℝ,
      SupportedCoefficients r (selectedA r v) ∧
      SupportedCoefficients r (selectedB r v) ∧
      LocalMaximalRanks r R C (selectedB r v) ∧
      ((matrixL r R C (selectedA r v)).submatrix
        (fun e : ↥α => e.1.1) (fun e : ↥α => e.1.2)).det ≠ 0 ∧
      (((matrixN r R C (selectedB r v))ᵀ).submatrix
        (fun e : ↥β => e.1.1) (fun e : ↥β => e.1.2)).det ≠ 0 ∧
      (matrixL r R C (selectedA r v)).rank = α.card ∧
      ((matrixN r R C (selectedB r v))ᵀ).rank = β.card := by sorry
