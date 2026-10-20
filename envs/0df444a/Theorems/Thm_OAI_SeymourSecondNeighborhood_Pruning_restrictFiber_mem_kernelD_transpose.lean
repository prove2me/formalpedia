-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_restrictFiber_mem_kernelD_transpose
-- name    : OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:29:09.740805+00:00
-- url     : https://prove2.me/theorems/196e28d9-da2c-40cd-a502-278e9a2dc580
-- title:
--   Kernel vectors of $N^{\mathsf T}$ restrict to kernel vectors of the transposed local matrices
-- statement:
--   Let $r$ be a relation on a finite set $X$, $R,C\subseteq X\times X$, and $b:X\times X\to\mathbb{R}$ coefficients supported on arcs ($b(x,y)=0$ unless $x\to y$). For an arc $p\to i$, the local matrix $D^{(p,i)}$ has rows indexed by the fibre $C_i=\{s:(i,s)\in C\}$, columns indexed by $R_p=\{j:(p,j)\in R\}$, and entries $b(s,j)$. The right-cover matrix $N$ has rows indexed by $C$, columns by the doubly covered pairs $Z(R,C)$, and entries $N_{\gamma,z}=b(\gamma_2,z_2)$ when $\gamma_1=z_1$, and $0$ otherwise.
--
--   Let $p\to i$ be an arc and $v\in\mathbb{R}^C$ with $N^{\mathsf T}v=0$. Then the restriction $v|_{C_i}$, $s\mapsto v(i,s)$, satisfies
--   $$
--   \bigl(D^{(p,i)}\bigr)^{\mathsf T}v|_{C_i}=0 .
--   $$
--
--   This is the dual counterpart of the hub-matrix restriction: left kernel vectors of the cover matrix become left kernel vectors of the local matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/KernelRestriction.lean#L101-L119

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

theorem OAI.SeymourSecondNeighborhood.Pruning.restrictFiber_mem_kernelD_transpose (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (hb : SupportedCoefficients r b)
    (p i : X) (hpi : r p i) (v : ↥C → ℝ)
    (hv : (matrixN r R C b)ᵀ *ᵥ v = 0) :
    (matrixD R C b p i)ᵀ *ᵥ restrictFiber C i v = 0 := by sorry
