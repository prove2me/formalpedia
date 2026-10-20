-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_LinearAlgebra_MaxSupportKernel_kernel_support_of_max_rank
-- name    : OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:29:47.977518+00:00
-- url     : https://prove2.me/theorems/cc48b325-3c83-4dc7-b112-cdee462abdd2
-- title:
--   For a maximal-rank matrix on a support, right and left kernel vectors cannot both be nonzero at a support position
-- statement:
--   Let $I,J$ be finite, $T\subseteq I\times J$, and $D\in\mathbb{R}^{I\times J}$ supported on $T$, of maximal rank among all real matrices supported on $T$. Let $x\in\mathbb{R}^J$ with $Dx=0$ and $y\in\mathbb{R}^I$ with $D^{\mathsf T}y=0$. Then for every $(s,j)\in T$,
--   $$
--   x_j\,y_s=0 .
--   $$
--
--   The supports of right and left kernel vectors of a generic matrix are separated by its support pattern. This is the linear-algebraic source of the conflict-freeness of the pruned pair sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MaxSupportKernel.lean#L57-L84

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.LinearAlgebra OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

theorem OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.kernel_support_of_max_rank {T : Set (I × J)} {D : Matrix I J ℝ}
    (hD : SupportedOn T D)
    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
    {x : J → ℝ} {y : I → ℝ}
    (hx : D *ᵥ x = 0) (hy : Dᵀ *ᵥ y = 0)
    {s : I} {j : J} (hsj : (s, j) ∈ T) :
    x j * y s = 0 := by sorry
