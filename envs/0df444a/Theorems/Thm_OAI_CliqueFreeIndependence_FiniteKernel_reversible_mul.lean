-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_reversible_mul
-- name    : OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:39:12.117988+00:00
-- url     : https://prove2.me/theorems/2deee309-364b-4668-87a6-ec5dcbc6df36
-- title:
--   Products of commuting reversible kernels are reversible
-- statement:
--   Let $I$ be a finite index set, let $\pi:I\to\mathbb R$, and let $P,Q$ be real $I\times I$ matrices (kernels). A kernel $P$ is *reversible* with respect to $\pi$ if it satisfies the detailed-balance equations
--
--   $$
--   \pi_i\,P_{ij}=\pi_j\,P_{ji}\qquad\text{for all }i,j\in I .
--   $$
--
--   If $P$ and $Q$ are both reversible with respect to $\pi$ and commute, $PQ=QP$, then the matrix product $PQ$ is reversible with respect to $\pi$, that is, $\pi_i\,(PQ)_{ij}=\pi_j\,(PQ)_{ji}$ for all $i,j\in I$. No nonnegativity, normalization or stochasticity is assumed.
--
--   This closure property shows that powers of a reversible kernel, and smoothed kernels of the form $P\,\big(\tfrac12(\mathrm{Id}+P)\big)^j$, are again reversible with respect to the same weight $\pi$.
--
--   **Formalization Note** Kernels are `Kernel I = Matrix I I ℝ`, the product is matrix multiplication, and commutation is `Commute P Q` in the matrix ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean#L99-L115

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
open FiniteEntropy
variable {I : Type u} [Fintype I]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI

theorem OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul {π : I → ℝ} {P Q : Kernel I}
    (hP : Reversible π P) (hQ : Reversible π Q) (hc : Commute P Q) :
    Reversible π (P * Q) := by sorry
