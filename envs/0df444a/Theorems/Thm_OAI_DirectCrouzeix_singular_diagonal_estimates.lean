-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_singular_diagonal_estimates
-- name    : OAI.DirectCrouzeix.singular_diagonal_estimates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:33:00.078298+00:00
-- url     : https://prove2.me/theorems/cca23c51-c615-4ea2-b325-f64b5ed4f06d
-- title:
--   Weighted bounds on the compressions $X^*b_k(A)X$ and $Y^*b_k(A)Y$ at a singular pair of a tensor polynomial
-- statement:
--   Throughout, $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carries its normalized Haar measure $dt$ (total mass $1$). For a complex matrix $M$, $M^*$ denotes its conjugate transpose, $\|M\|$ its operator norm with respect to the Euclidean norms, and $\|M\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(M^*M)=\sum_{i,j}|M_{ij}|^2$ its squared Hilbert–Schmidt (Frobenius) norm. For a continuous matrix-valued function $\Phi$ on $\mathbb{T}$ and $k\in\mathbb{Z}$, $\widehat\Phi(k)=\int_{\mathbb{T}}e^{-2\pi i k t}\,\Phi(t)\,dt$ is its $k$-th Fourier coefficient.
--
--   Let $n,m\in\mathbb{N}$ and $A\in M_n(\mathbb{C})$. Write $M_m(\mathbb{C})[z]$ for the ring of polynomials with coefficients in $M_m(\mathbb{C})$. For $G(z)=\sum_j z^jG_j$ in this ring and $\lambda\in\mathbb{C}$ set $G(\lambda)=\sum_j\lambda^jG_j\in M_m(\mathbb{C})$, and
--   $$
--   G(A)=\sum_j A^j\otimes G_j\in M_{nm}(\mathbb{C}),
--   $$
--   where $\otimes$ is the Kronecker product. The matrix $G(A)$ acts on $\mathbb{C}^n\otimes\mathbb{C}^m=\mathbb{C}^{n\times m}$, and an $n\times m$ matrix $X$ is regarded as the vector $\operatorname{vec}(X)\in\mathbb{C}^{n\times m}$ of its entries. Fix scalar polynomials $b_0,b_1,b_2,\dots\in\mathbb{C}[z]$. For $N\in\mathbb{N}$ and $C=(C_0,\dots,C_{N-1})\in M_m(\mathbb{C})^N$ put $G_C(z)=\sum_{k<N}b_k(z)\,C_k$. For $h:\mathbb{T}\to\mathbb{C}$ define the boundary energy $\mathcal{E}_h(G)=\int_{\mathbb{T}}\|G(h(t))\|_{\mathrm{HS}}^2\,dt$, and let $w_0=1$ and $w_k=2$ for $k\ge1$.
--
--   Assume:
--   1. $h$ is continuous, and every $G\in M_m(\mathbb{C})[z]$ equals $G_C$ for some $N$ and some $C\in M_m(\mathbb{C})^N$. Moreover, for every $N$ and every $C\in M_m(\mathbb{C})^N$,
--   $$
--   \sum_{k<N}\|C_k\|_{\mathrm{HS}}^2\le\mathcal{E}_h(G_C)\le\sum_{k<N}w_k\,\|C_k\|_{\mathrm{HS}}^2 ;
--   $$
--   2. $R:\mathbb{T}\to M_n(\mathbb{C})$ is continuous and $\widehat R(-k)=b_k(A)$ for every $k\in\mathbb{N}$;
--   3. $F\in M_m(\mathbb{C})[z]$ satisfies $\|F(h(t))\|\le1$ for every $t\in\mathbb{T}$;
--   4. $X,Y$ are complex $n\times m$ matrices and $\gamma>0$ is a real number with $F(A)\operatorname{vec}(X)=\gamma\operatorname{vec}(Y)$ and $F(A)^*\operatorname{vec}(Y)=\gamma\operatorname{vec}(X)$.
--
--   Put $a=\int_{\mathbb{T}}\|Y^*R(t)X\|_{\mathrm{HS}}^2\,dt$. Then
--   $$
--   \|X^*b_0(A)X\|_{\mathrm{HS}}^2+\frac12\sum_{k=1}^{\infty}\|X^*b_k(A)X\|_{\mathrm{HS}}^2\le\frac{a}{\gamma^2}
--   \qquad\text{and}\qquad
--   \|Y^*b_0(A)Y\|_{\mathrm{HS}}^2+\frac12\sum_{k=1}^{\infty}\|Y^*b_k(A)Y\|_{\mathrm{HS}}^2\le\frac{a}{\gamma^2}.
--   $$
--
--   Condition 4 says that, unless $X=Y=0$, the vectors $\operatorname{vec}(X)$ and $\operatorname{vec}(Y)$ are right and left singular vectors of $F(A)$ for the singular value $\gamma$. The theorem converts this extremal structure into quantitative control of the $m\times m$ compressions of the operators $b_k(A)$ to $X$ and to $Y$, all measured by the single off-diagonal boundary energy $a$. It is applied to the largest singular value in the proof of the bound $\|F(A)\|\le2$, where these two inequalities are compared with Parseval's identity for $t\mapsto X^*R(t)X$ and $t\mapsto Y^*R(t)Y$.
--
--   **Formalization Note** The squared Hilbert–Schmidt norm is `hsSq`, $G(\lambda)$ is `matrixPolynomialValue λ G`, $G(A)$ is `tensorPolynomial A G`, $G_C$ is `faberPolynomial b C`, $\mathcal{E}_h$ is `polynomialEnergy h` and $w_k$ is `faberWeight k`. Fourier coefficients are Mathlib's `fourierCoeff` on `AddCircle (1 : ℝ)` with `haarAddCircle`; the matrix norm is the $L^2$ operator norm (`Matrix.Norms.L2Operator`); $\operatorname{vec}(X)$ is `hsVector X`, and $F(A)^*$ is `ContinuousLinearMap.adjoint` of `Matrix.toEuclideanCLM (tensorPolynomial A F)`. The infinite series are Lean `tsum`s over $k+1$ with $k\in\mathbb{N}$ (for a non-summable family `tsum` would be $0$). No positivity of $n$ or $m$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean#L165-L219

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory

theorem OAI.DirectCrouzeix.singular_diagonal_estimates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) (hsVector X) =
      (γ : ℂ) • hsVector Y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) (hsVector Y) =
      (γ : ℂ) • hsVector X) :
    let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
    (hsSq (Xᴴ * Polynomial.aeval A (b 0) * X) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Xᴴ * Polynomial.aeval A (b (k+1)) * X) ≤ a / γ^2) ∧
    (hsSq (Yᴴ * Polynomial.aeval A (b 0) * Y) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Yᴴ * Polynomial.aeval A (b (k+1)) * Y) ≤ a / γ^2) := by sorry
