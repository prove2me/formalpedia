-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_cross_boundary_estimate
-- name    : OAI.DirectCrouzeix.cross_boundary_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:32:28.684972+00:00
-- url     : https://prove2.me/theorems/04056427-e0ec-4b60-96cf-d70e32a70b97
-- title:
--   Boundary-energy bound for matrix coefficients of the tensor polynomial calculus
-- statement:
--   **Setting.** Let $n,m\ge0$ be integers and $A$ a complex $n\times n$ matrix. Write $M_m(\mathbb{C})$ for the complex $m\times m$ matrices, $M^*$ for the conjugate transpose and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ for the squared Hilbert–Schmidt norm.
--
--   - *Circle.* $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ with its normalized Haar measure $dt$ (total mass $1$). For a continuous $F:\mathbb{T}\to M_n(\mathbb{C})$ the Fourier coefficients are $\widehat{F}(j)=\int_{\mathbb{T}}e^{-2\pi ijt}F(t)\,dt$ for $j\in\mathbb{Z}$.
--   - *Matrix polynomials.* $G=\sum_jG_j\lambda^j$ with coefficients $G_j\in M_m(\mathbb{C})$. Its values are $G(z)=\sum_jz^jG_j\in M_m(\mathbb{C})$ for $z\in\mathbb{C}$, and its tensor evaluation at $A$ is $G[A]=\sum_jA^j\otimes G_j$, where $\otimes$ is the Kronecker product, $(A\otimes C)_{(i,j),(k,l)}=A_{ik}C_{jl}$, acting on $\mathbb{C}^{[n]\times[m]}$ with $[n]=\{1,\dots,n\}$.
--   - *Expansions.* Fix polynomials $b_0,b_1,b_2,\ldots\in\mathbb{C}[\lambda]$, and let $b_k(A)$ denote the usual polynomial calculus of $A$. For $N\in\mathbb{N}$ and $C=(C_0,\dots,C_{N-1})$ in $M_m(\mathbb{C})$ let $\Phi_b(C)=\sum_{k<N}C_k\,b_k(\lambda)$, the matrix polynomial with values $\Phi_b(C)(z)=\sum_{k<N}b_k(z)\,C_k$.
--   - *Energy.* Fix an arbitrary function $h:\mathbb{T}\to\mathbb{C}$ and set $\mathcal{E}_h(G)=\int_{\mathbb{T}}\|G(h(t))\|_{\mathrm{HS}}^2\,dt$.
--   - *Vectors.* For an $n\times m$ matrix $X$, $\operatorname{vec}X\in\mathbb{C}^{[n]\times[m]}$ has entries $(\operatorname{vec}X)_{(i,j)}=X_{ij}$, and $\langle x,y\rangle=\sum_p\overline{x_p}\,y_p$.
--
--   **Hypotheses.** (i) Every matrix polynomial $G$ with coefficients in $M_m(\mathbb{C})$ equals $\Phi_b(C)$ for some $N$ and some $C_0,\dots,C_{N-1}$. (ii) For every $N$ and all $C_0,\dots,C_{N-1}$, $\sum_{k<N}\|C_k\|_{\mathrm{HS}}^2\le\mathcal{E}_h(\Phi_b(C))$. (iii) $R:\mathbb{T}\to M_n(\mathbb{C})$ is continuous and $\widehat{R}(-k)=b_k(A)$ for every $k\in\mathbb{N}$.
--
--   **Conclusion.** For all complex $n\times m$ matrices $X,Y$ and every matrix polynomial $G$ with coefficients in $M_m(\mathbb{C})$,
--   $$\bigl|\langle\operatorname{vec}Y,\ G[A]\operatorname{vec}X\rangle\bigr|^2\le\Bigl(\int_{\mathbb{T}}\|Y^*R(t)X\|_{\mathrm{HS}}^2\,dt\Bigr)\,\mathcal{E}_h(G).$$
--
--   The estimate bounds every matrix coefficient of the tensor calculus $G\mapsto G[A]$ by the boundary energy of $G$ along $h$, times an integral of a compression of the boundary function $R$. In the application the $b_k$ form a Faber-type polynomial basis attached to a domain, $h$ traces the boundary of that domain, and (ii) is a lower energy estimate for expansions in this basis.
--
--   **Formalization Note** $\mathbb{T}$ is `BoundaryCircle` (that is, `AddCircle 1`) with `circleMeasure`, the Haar probability measure; $\widehat{F}(j)$ is Mathlib's `fourierCoeff F j`; $\Phi_b(C)$ is `faberPolynomial b C`, $\mathcal{E}_h$ is `polynomialEnergy h`, $G[A]$ is `tensorPolynomial A G`, $\operatorname{vec}$ is `hsVector`, and $b_k(A)$ is `Polynomial.aeval A (b k)`. No regularity is assumed on $h$; the integrals are Bochner integrals, which by Lean's convention equal $0$ for non-integrable integrands, and hypothesis (ii) is understood with the same convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean#L121-L144

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

theorem OAI.DirectCrouzeix.cross_boundary_estimate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (X Y : Matrix (Fin n) (Fin m) ℂ) (G : MatrixPolynomial m) :
    ‖inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A G) (hsVector X))‖ ^ 2 ≤
      (∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure) * polynomialEnergy h G := by sorry
