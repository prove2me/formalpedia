-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_weighted_coefficient_dual
-- name    : OAI.DirectCrouzeix.weighted_coefficient_dual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:28:16.069982+00:00
-- url     : https://prove2.me/theorems/9174c3de-5d1d-4fc7-9571-9e46bb77f7c2
-- title:
--   Weighted duality bound for a finite family of matrix coefficients
-- statement:
--   Let $\rho,\iota,\kappa$ be finite index sets and let $(P_k)_{k\in\rho}$ be complex $\iota\times\kappa$ matrices. For $\iota\times\kappa$ matrices $M,C$ write $\langle\!\langle M,C\rangle\!\rangle=\sum_{i,j}M_{ij}C_{ij}$ for the bilinear entrywise pairing and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ for the squared Hilbert–Schmidt norm. Let $(w_k)_{k\in\rho}$ be strictly positive real weights and let $b\ge0$. Assume that for every family $(C_k)_{k\in\rho}$ of complex $\iota\times\kappa$ matrices
--   $$\Bigl|\sum_{k\in\rho}\langle\!\langle P_k,C_k\rangle\!\rangle\Bigr|^2\le b\sum_{k\in\rho}w_k\,\|C_k\|_{\mathrm{HS}}^2 .$$
--   Then
--   $$\sum_{k\in\rho}\frac{\|P_k\|_{\mathrm{HS}}^2}{w_k}\le b .$$
--
--   This is the elementary half of the duality between the weighted Hilbert–Schmidt norms with weights $w_k$ and $1/w_k$: if the linear functional $(C_k)\mapsto\sum_k\langle\!\langle P_k,C_k\rangle\!\rangle$ has squared norm at most $b$ for the weighted norm $\sum_kw_k\|C_k\|_{\mathrm{HS}}^2$, then the representing family $(P_k)$ has squared dual norm at most $b$. It turns pairing estimates against arbitrary test coefficients into bounds on the coefficients $P_k$ themselves.
--
--   **Formalization Note** $\langle\!\langle\cdot,\cdot\rangle\!\rangle$ is `entryPair` and $\|M\|_{\mathrm{HS}}^2$ is `hsSq M`, defined as $\operatorname{Re}\operatorname{tr}(M^*M)$; the absolute value on the left of the hypothesis is the complex modulus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Duality.lean#L15-L46

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

open OAI OAI.DirectCrouzeix
universe u_41 u_42 u_43 u_44 u_45
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.weighted_coefficient_dual {ρ : Type u_41} {ι : Type u_42} {κ : Type u_43}
    [Fintype ρ] [Fintype ι] [Fintype κ]
    (P : ρ → Matrix ι κ ℂ) (w : ρ → ℝ) (hw : ∀ k, 0 < w k)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ C : ρ → Matrix ι κ ℂ,
      ‖∑ k, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k, w k * hsSq (C k)) :
    (∑ k, hsSq (P k) / w k) ≤ b := by sorry
