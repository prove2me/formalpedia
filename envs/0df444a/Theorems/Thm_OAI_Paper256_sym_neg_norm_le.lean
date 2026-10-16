-- Prove2me | Theorems.Thm_OAI_Paper256_sym_neg_norm_le
-- name    : OAI.Paper256.sym_neg_norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:08:27.35826+00:00
-- url     : https://prove2.me/theorems/0a34709f-9a90-48e9-9c08-50eb6cf7ca93
-- title:
--   A symmetric matrix is bounded below by minus its operator norm times the identity
-- statement:
--   Let $X$ be a real symmetric $n\times n$ matrix and let $\|X\|$ be its operator norm with respect to the Euclidean norm on $\mathbb{R}^n$ (the spectral norm). Then, in the Loewner order,
--   $$-\|X\|\,I_n\preceq X,$$
--   that is, $X+\|X\|\,I_n$ is positive semidefinite. Here $A\preceq B$ means that $B-A$ is positive semidefinite.
--
--   Equivalently, every eigenvalue of $X$ is at least $-\|X\|$. The bound is used to show that a small symmetric perturbation of a positive definite matrix remains positive definite, i.e. that the positive definite matrices form an open set.
--
--   **Formalization Note** The norm is the scoped instance `Matrix.Norms.L2Operator` and the order on matrices is the Loewner order of the scoped `MatrixOrder` instance. The degenerate case $n=0$ is included.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilOrder.lean#L12-L24

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

theorem OAI.Paper256.sym_neg_norm_le {n : ℕ} (X : Sym n) :
    -(‖(X : Mat n ℝ)‖) • (1 : Mat n ℝ) ≤ (X : Mat n ℝ) := by sorry
