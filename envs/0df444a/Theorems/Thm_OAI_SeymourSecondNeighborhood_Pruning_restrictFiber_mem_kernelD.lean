-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_restrictFiber_mem_kernelD
-- name    : OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:28:38.157045+00:00
-- url     : https://prove2.me/theorems/56b0c6c9-d54a-4ca3-93b7-5b8adb52b988
-- title:
--   Kernel vectors of the hub matrix restrict to kernel vectors of the local matrices
-- statement:
--   Let $r$ be a relation on a finite set $X$, $R,C\subseteq X\times X$, and $b:X\times X\to\mathbb{R}$ coefficients supported on arcs ($b(x,y)=0$ unless $x\to y$). For an arc $p\to i$, the local matrix $D^{(p,i)}$ has rows indexed by the fibre $C_i=\{s:(i,s)\in C\}$, columns indexed by $R_p=\{j:(p,j)\in R\}$, and entries $b(s,j)$. The hub matrix $B$ has rows indexed by the hub pairs $H(R,C)$, columns by $R$, and entries $B_{h,\rho}=b(h_2,\rho_2)$ when $h_1=\rho_1$, and $0$ otherwise.
--
--   Let $p\to i$ be an arc and $u\in\mathbb{R}^R$ with $Bu=0$. Then the restriction $u|_{R_p}$, $j\mapsto u(p,j)$, satisfies
--   $$
--   D^{(p,i)}\,u|_{R_p}=0 .
--   $$
--
--   Global kernel vectors therefore induce local kernel vectors on every fibre, which is how local rank information constrains global kernels.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean#L82-L99

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

open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Matrix
open scoped BigOperators
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (hb : SupportedCoefficients r b) (p i : X)
    (hpi : r p i) (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0) :
    matrixD R C b p i *ᵥ restrictFiber R p u = 0 := by sorry
