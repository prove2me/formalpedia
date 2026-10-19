-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_tensor_entryPair
-- name    : OAI.DirectCrouzeix.tensor_entryPair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:27:45.397529+00:00
-- url     : https://prove2.me/theorems/65eb1d76-771e-4cbc-9c11-dd0e99ab4c59
-- title:
--   Matrix coefficients of a Kronecker product as an entrywise pairing with a compression
-- statement:
--   Let $n,m\ge0$ be integers, $A$ a complex $n\times n$ matrix, $C$ a complex $m\times m$ matrix, and $X,Y$ complex $n\times m$ matrices. With $[n]=\{1,\dots,n\}$, identify an $n\times m$ matrix $X$ with the vector $\operatorname{vec}X\in\mathbb{C}^{[n]\times[m]}$, $(\operatorname{vec}X)_{(i,j)}=X_{ij}$, and give $\mathbb{C}^{[n]\times[m]}$ the inner product $\langle x,y\rangle=\sum_p\overline{x_p}\,y_p$. The Kronecker product $A\otimes C$ acts on this space through its entries $(A\otimes C)_{(i,j),(k,l)}=A_{ik}C_{jl}$. For $m\times m$ matrices $M,N$ let $\langle\!\langle M,N\rangle\!\rangle=\sum_{j,l}M_{jl}N_{jl}=\operatorname{tr}(MN^{\top})$ be the bilinear entrywise pairing (no complex conjugation). Then
--   $$\langle\operatorname{vec}Y,\,(A\otimes C)\operatorname{vec}X\rangle=\langle\!\langle Y^*AX,\,C\rangle\!\rangle,$$
--   where $Y^*$ is the conjugate transpose of $Y$, so that $Y^*AX$ is an $m\times m$ matrix.
--
--   The identity separates the two tensor factors: a matrix coefficient of $A\otimes C$ between vectors of $\mathbb{C}^n\otimes\mathbb{C}^m$ is the pairing of the compression $Y^*AX$ with the coefficient $C$. Summed over $k$, it rewrites $\langle\operatorname{vec}Y,(\sum_kA^k\otimes B_k)\operatorname{vec}X\rangle$ as $\sum_k\langle\!\langle Y^*A^kX,B_k\rangle\!\rangle$, which is how matrix coefficients of the tensor polynomial calculus are reduced to compressions of polynomials in $A$.
--
--   **Formalization Note** $\operatorname{vec}$ is `hsVector`, with values in `EuclideanSpace ℂ (Fin n × Fin m)`; $A\otimes C$ is the Kronecker product `A ⊗ₖ C` acting through `Matrix.toEuclideanCLM`; $\langle\!\langle\cdot,\cdot\rangle\!\rangle$ is `entryPair`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean#L88-L113

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

open OAI OAI.DirectCrouzeix
universe u_37 u_38 u_39 u_40
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.tensor_entryPair {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y)
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (A ⊗ₖ C) (hsVector X)) =
      entryPair (Yᴴ * A * X) C := by sorry
