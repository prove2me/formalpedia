-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_hsSq_mul_le
-- name    : OAI.DirectCrouzeix.hsSq_mul_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:26:35.370893+00:00
-- url     : https://prove2.me/theorems/2de8f559-13ec-4c65-bb55-b580c629639d
-- title:
--   Hilbert–Schmidt norm of a product is at most the operator norm times the Hilbert–Schmidt norm
-- statement:
--   Let $\iota,\kappa,\tau$ be finite index sets, $F$ a complex $\iota\times\kappa$ matrix and $G$ a complex $\kappa\times\tau$ matrix. Write $\|M\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(M^*M)=\sum_{i,j}|M_{ij}|^2$ for the squared Hilbert–Schmidt (Frobenius) norm, and let
--   $$\|F\|=\sup\{\|Fx\|:\ x\in\mathbb{C}^{\kappa},\ \|x\|\le1\}$$
--   be the operator norm of $F$ as a map from $\mathbb{C}^{\kappa}$ to $\mathbb{C}^{\iota}$, both with Euclidean norms (the largest singular value of $F$). Then
--   $$\|FG\|_{\mathrm{HS}}^2\le\|F\|^2\,\|G\|_{\mathrm{HS}}^2 .$$
--
--   This is the ideal property of the Hilbert–Schmidt norm with respect to left multiplication by a bounded operator; the mirror inequality $\|GF\|_{\mathrm{HS}}\le\|G\|_{\mathrm{HS}}\|F\|$ follows by taking adjoints. It is used pointwise along a boundary curve to show that multiplying a matrix polynomial by another one whose values have operator norm at most $1$ does not increase the integrated squared Hilbert–Schmidt norm.
--
--   **Formalization Note** $\|M\|_{\mathrm{HS}}^2$ is `hsSq M`. The operator norm is the $L^2$ operator norm on matrices made available by `open scoped Matrix.Norms.L2Operator`; it requires decidable equality on the column index type $\kappa$, which is why the statement assumes it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean#L62-L83

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt

open OAI OAI.DirectCrouzeix
universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.hsSq_mul_le {ι : Type u_24} {κ : Type u_25} {τ : Type u_26} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ ‖F‖ ^ 2 * hsSq G := by sorry
