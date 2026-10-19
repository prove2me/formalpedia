-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_weighted_sequence_dual
-- name    : OAI.DirectCrouzeix.weighted_sequence_dual
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:30:28.879857+00:00
-- url     : https://prove2.me/theorems/48df0f67-b5d2-446e-b627-6b0f761bd188
-- title:
--   Duality bound for a sequence of matrices with weights $1,2,2,\dots$
-- statement:
--   Let $\iota,\kappa$ be finite index sets and $(P_k)_{k\ge0}$ a sequence of complex $\iota\times\kappa$ matrices. Write $\langle\!\langle M,C\rangle\!\rangle=\sum_{i,j}M_{ij}C_{ij}$ for the bilinear entrywise pairing and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ for the squared Hilbert–Schmidt norm, and define the weights $w_0=1$ and $w_k=2$ for $k\ge1$. Let $b\ge0$ and assume that for every $N\in\mathbb{N}$ and all complex $\iota\times\kappa$ matrices $C_0,\dots,C_{N-1}$
--   $$\Bigl|\sum_{k=0}^{N-1}\langle\!\langle P_k,C_k\rangle\!\rangle\Bigr|^2\le b\sum_{k=0}^{N-1}w_k\,\|C_k\|_{\mathrm{HS}}^2 .$$
--   Then
--   $$\|P_0\|_{\mathrm{HS}}^2+\frac12\sum_{n=0}^{\infty}\|P_{n+1}\|_{\mathrm{HS}}^2\le b .$$
--
--   This is the infinite-sequence form of the weighted duality bound for the specific weights $1,2,2,\dots$. These are the weights of an upper estimate $\|C_0\|_{\mathrm{HS}}^2+2\sum_{k\ge1}\|C_k\|_{\mathrm{HS}}^2$ for the integrated squared Hilbert–Schmidt norm, along a boundary curve, of an expansion $\sum_kC_kb_k$ in a polynomial basis $(b_k)$; the bound is applied to compressions $P_k=X^*b_k(A)X$ of the basis polynomials evaluated at a matrix $A$, and yields square-summability of these compressions with an explicit constant.
--
--   **Formalization Note** The weights are `faberWeight k`. The infinite sum is Mathlib's `tsum`, which is $0$ for a non-summable series; under the hypothesis the series of nonnegative terms has bounded partial sums, so it converges and the displayed sum is the genuine sum of the series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryEnergy.lean#L112-L133

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy

open OAI OAI.DirectCrouzeix
universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory

theorem OAI.DirectCrouzeix.weighted_sequence_dual {ι : Type u_85} {κ : Type u_86} [Fintype ι] [Fintype κ]
    (P : ℕ → Matrix ι κ ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ N (C : Fin N → Matrix ι κ ℂ),
      ‖∑ k : Fin N, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k : Fin N, faberWeight k * hsSq (C k)) :
    hsSq (P 0) + (1/2 : ℝ) * ∑' n : ℕ, hsSq (P (n+1)) ≤ b := by sorry
