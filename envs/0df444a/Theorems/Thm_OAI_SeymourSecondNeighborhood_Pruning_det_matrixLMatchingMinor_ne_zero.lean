-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_det_matrixLMatchingMinor_ne_zero
-- name    : OAI.SeymourSecondNeighborhood.Pruning.det_matrixLMatchingMinor_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:30:50.230423+00:00
-- url     : https://prove2.me/theorems/f3a2033d-b308-4fc7-9c98-f51f7238bba1
-- title:
--   The matching minor of the variable left-cover matrix has nonzero determinant
-- statement:
--   Let $r$ be a relation on a finite set $X$, read as a digraph with arcs $x\to y$, and let $R,C\subseteq X\times X$. A pair $\rho\in R$ left-covers $z$ if $\rho_2=z_2$ and $\rho_1\to z_1$. A pair $\gamma\in C$ right-covers $z$ if $\gamma_1=z_1$ and $\gamma_2\to z_2$. $Z=Z(R,C)$ is the set of pairs that are left-covered by $R$ and right-covered by $C$. $\rho\in R$ and $\gamma\in C$ conflict if $\rho_1\to\gamma_1$ and $\gamma_2\to\rho_2$. $H=H(R,C)$ is the set of hub pairs $h$ for which there are $i,j$ with $(h_1,j)\in R$, $(i,h_2)\in C$, $h_1\to i$ and $h_2\to j$. Let $\mathcal{L}$ be the $Z\times R$ matrix of polynomials whose entry at $(z,\rho)$ is the variable $X_{a,(\rho_1,z_1)}$ when $\rho$ left-covers $z$, and $0$ otherwise.
--
--   Let $M\subseteq Z\times R$ be a matching in the left-cover relation. Let $\mathcal{L}_M$ be the $M\times M$ matrix with entry $\mathcal{L}_{z_e,\rho_f}$ at $(e,f)$, where $e=(z_e,\rho_e)$ and $f=(z_f,\rho_f)$. Then
--   $$
--   \det\mathcal{L}_M\ne0
--   $$
--   as a polynomial over $\mathbb{R}$.
--
--   A generic evaluation of $\mathcal{L}$ is therefore nonsingular on every matching. This makes the rank of the real left-cover matrix at least the size of a maximum matching.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankGlobalMinors.lean#L63-L92

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
open scoped Matrix
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.SeymourSecondNeighborhood.Pruning.det_matrixLMatchingMinor_ne_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥R))
    (hM : Bipartite.IsMatching (matrixLSupport r R C) M) :
    (matrixLMatchingMinor r R C M).det ≠ 0 := by sorry
