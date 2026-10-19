-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_positive_block_hsSq
-- name    : OAI.DirectCrouzeix.positive_block_hsSq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:25:17.617981+00:00
-- url     : https://prove2.me/theorems/006029e0-c97d-4c4c-9fb5-5de1eaac31aa
-- title:
--   Hilbert–Schmidt bound for the off-diagonal block of a positive semidefinite block matrix
-- statement:
--   Let $\iota$ be a finite index set and let $U,V,Z$ be complex $\iota\times\iota$ matrices. Write $M^*$ for the conjugate transpose of a matrix $M$ and $\|M\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(M^*M)=\sum_{i,j}|M_{ij}|^2$ for its squared Hilbert–Schmidt (Frobenius) norm. Suppose that the $2\times2$ block matrix
--   $$D=\begin{pmatrix}U&Z^*\\ Z&V\end{pmatrix},$$
--   indexed by two disjoint copies of $\iota$, is positive semidefinite, that is, Hermitian with $\langle x,Dx\rangle\ge0$ for every vector $x$. Then
--   $$2\,\|Z\|_{\mathrm{HS}}^2\le\|U\|_{\mathrm{HS}}^2+\|V\|_{\mathrm{HS}}^2.$$
--
--   The inequality says that the off-diagonal block of a positive block matrix is controlled, in Hilbert–Schmidt norm, by its diagonal blocks. It is applied pointwise to positive block matrices built from compressions $X^*RX$, $Y^*RY$, $Y^*RX$ of a matrix $R$ whose Hermitian part is positive semidefinite, in order to bound a cross term by two diagonal terms.
--
--   **Formalization Note** The block matrix is `Matrix.fromBlocks U Zᴴ Z V`, indexed by `ι ⊕ ι`, and positivity is `Matrix.PosSemidef`. $\|M\|_{\mathrm{HS}}^2$ is `hsSq M`, defined as the real part of the trace of $M^*M$. The index type is assumed to have decidable equality, a technical requirement for identity matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean#L35-L62

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks

open OAI OAI.DirectCrouzeix
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.positive_block_hsSq {ι : Type u_7} [Fintype ι] [DecidableEq ι]
    {U V Z : Matrix ι ι ℂ}
    (h : (Matrix.fromBlocks U Zᴴ Z V).PosSemidef) :
    2 * hsSq Z ≤ hsSq U + hsSq V := by sorry
