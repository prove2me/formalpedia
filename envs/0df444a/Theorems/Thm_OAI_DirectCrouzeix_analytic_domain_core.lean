-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_analytic_domain_core
-- name    : OAI.DirectCrouzeix.analytic_domain_core
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:33:36.533019+00:00
-- url     : https://prove2.me/theorems/eeacfdd7-b85b-4515-a46e-8194e7667620
-- title:
--   Norm bound $\|F(A)\|\le 2$ for tensor matrix polynomials from a positive boundary representation of $A$
-- statement:
--   **Notation.** $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carries its normalized Haar measure $dt$. For a complex matrix $M$, $M^*$ is its conjugate transpose, $\|M\|$ its operator norm for the Euclidean norms, and $\|M\|_{\mathrm{HS}}^2=\sum_{i,j}|M_{ij}|^2$ its squared Hilbert–Schmidt norm. For a continuous matrix-valued $\Phi$ on $\mathbb{T}$ and $k\in\mathbb{Z}$, $\widehat\Phi(k)=\int_{\mathbb{T}}e^{-2\pi ikt}\,\Phi(t)\,dt$. Let $M_m(\mathbb{C})[z]$ be the ring of polynomials with coefficients in $M_m(\mathbb{C})$. For $G(z)=\sum_jz^jG_j$ in it, $\lambda\in\mathbb{C}$ and $A\in M_n(\mathbb{C})$, put $G(\lambda)=\sum_j\lambda^jG_j$ and $G(A)=\sum_jA^j\otimes G_j\in M_{nm}(\mathbb{C})$ (Kronecker products). Given scalar polynomials $b_0,b_1,\dots$ and $C=(C_0,\dots,C_{N-1})\in M_m(\mathbb{C})^N$, let $G_C(z)=\sum_{k<N}b_k(z)\,C_k$. Given $h:\mathbb{T}\to\mathbb{C}$, let $\mathcal{E}_h(G)=\int_{\mathbb{T}}\|G(h(t))\|_{\mathrm{HS}}^2\,dt$. Finally, let $w_0=1$ and $w_k=2$ for $k\ge1$.
--
--   Let $n,m\ge1$, $A\in M_n(\mathbb{C})$, let $b_0,b_1,b_2,\dots\in\mathbb{C}[z]$ with $b_0=1$, and let $h:\mathbb{T}\to\mathbb{C}$ be continuous. Assume:
--   1. (expansion and energy bounds) every $G\in M_m(\mathbb{C})[z]$ equals $G_C$ for some $N$ and $C$, and $\sum_{k<N}\|C_k\|_{\mathrm{HS}}^2\le\mathcal{E}_h(G_C)\le\sum_{k<N}w_k\|C_k\|_{\mathrm{HS}}^2$ for every $N$ and every $C\in M_m(\mathbb{C})^N$;
--   2. (boundary representation) $R:\mathbb{T}\to M_n(\mathbb{C})$ is continuous, $\widehat R(-k)=b_k(A)$ for every $k\in\mathbb{N}$, and $\widehat R(k)=0$ for every integer $k>0$;
--   3. (positivity) $R(t)+R(t)^*$ is positive semidefinite for every $t\in\mathbb{T}$.
--
--   Then every $F\in M_m(\mathbb{C})[z]$ with $\|F(h(t))\|\le1$ for all $t\in\mathbb{T}$ satisfies
--   $$
--   \|F(A)\|=\Big\|\sum_jA^j\otimes F_j\Big\|\le2 .
--   $$
--
--   The hypotheses package the data of a domain. Here $h$ plays the role of a boundary parametrization, and $(b_k)$ is a polynomial basis whose boundary energy is comparable to the coefficient norms with constants $1$ and $2$. Finally, $R$ is a continuous matrix-valued function with positive semidefinite real part, without positive frequencies, whose negative Fourier coefficients reproduce $b_k(A)$. Under these assumptions every matrix-coefficient polynomial bounded by $1$ in operator norm along the curve $h$ has tensor evaluation at $A$ of norm at most $2$. This is the abstract form of the constant-$2$ estimate for tensor evaluations $\sum_kA^k\otimes B_k$; to use it one has to construct $h$, $(b_k)$ and $R$ for the matrix and the domain at hand.
--
--   **Formalization Note** $F(A)$ is `tensorPolynomial A F`, $F(\lambda)$ is `matrixPolynomialValue λ F`, $G_C$ is `faberPolynomial b C`, $\mathcal{E}_h$ is `polynomialEnergy h`, $\|\cdot\|_{\mathrm{HS}}^2$ is `hsSq` and $w_k$ is `faberWeight k`. Matrix norms are $L^2$ operator norms (`Matrix.Norms.L2Operator`), positivity is `Matrix.PosSemidef`, and Fourier coefficients are Mathlib's `fourierCoeff` on `AddCircle (1 : ℝ)` with `haarAddCircle`. The condition $b_0=1$ means that $b_0$ is the constant polynomial $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DomainCore.lean#L15-L117

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

theorem OAI.DirectCrouzeix.analytic_domain_core {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (b : ℕ → Polynomial ℂ) (hb0 : b 0 = 1)
    (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (hposfreq : ∀ k : ℤ, 0 < k → fourierCoeff R k = 0)
    (hpositive : ∀ t, (R t + (R t)ᴴ).PosSemidef)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by sorry
