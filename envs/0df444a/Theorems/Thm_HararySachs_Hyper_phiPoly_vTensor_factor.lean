-- Prove2me | Theorems.Thm_HararySachs_Hyper_phiPoly_vTensor_factor
-- name    : HararySachs.Hyper.phiPoly_vTensor_factor
-- status  : Open
-- author  : @milia
-- created : 2026-11-13T04:34:02.261323+00:00
-- url     : https://prove2.me/theorems/cf6f6d3f-6ca8-4c6b-a525-63ae2dd9e897
-- title:
--   Factorisation of the resultant of the power system
-- statement:
--   Let $n \ge 1$, $k \ge 2$, $r = k-1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degree $r$ in $n$ variables, normalized by $\operatorname{Res}(x_1^r,\dots,x_n^r) = 1$. Let $V = (V_{ij})$ be an $n\times n$ matrix of indeterminates and let
--   $$\Phi_V(z) = \operatorname{Res}\bigl(x_i^{r} - z\,(Vx)_i^{r}\bigr)_{i=1}^n \in \mathbb{Q}[V][z].$$
--   Let $\xi = e^{2\pi i/r}$. Then, as polynomials in $\zeta$ over $\mathbb{C}[V]$,
--   $$\Phi_V(\zeta^r) = \prod_{\Omega}\det\bigl(I - \zeta\,\Omega V\bigr),$$
--   where $\Omega$ runs over the $r^n$ diagonal matrices $\operatorname{diag}(\xi^{\omega_1},\dots,\xi^{\omega_n})$ with $0 \le \omega_i < r$.
--
--   This is the power-system case of the identity $\log\operatorname{Res} = \operatorname{tr}\log$. The forms $x_i^r - \zeta^r (Vx)_i^r$ factor into the linear forms $x_i - \zeta\,\xi^{\omega_i}(Vx)_i$, and each choice of factors contributes a determinant.
--
--   **Formalization Note** The power system is `zcoord (vTensor n k)` and $\Phi_V$ is `phiPoly (vTensor n k) res`. The coefficients are mapped from $\mathbb{Q}$ to $\mathbb{C}$, and $\Phi_V(\zeta^r)$ is `Polynomial.comp` with `X ^ (k - 1)`. The product is over `Ω : Fin n → Fin (k - 1)`, and $\det(I - \zeta N)$ is `Matrix.charpolyRev N`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 2 (the matrix case $\operatorname{Res} = \prod\det$); mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and 5f345eb5-bd58-46fc-8bd2-52a8bf0241e1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- Factorisation of the power system `x_i^r = z (V x)_i^r` (`r = k - 1`):
`Φ_V(ζ^r) = ∏_{Ω ∈ μ_r^n} det(I - ζ Ω V)` as polynomials in `ζ` over `ℂ[V]`. -/
theorem phiPoly_vTensor_factor (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    ((phiPoly (k := k) (vTensor n k) res).map (MvPolynomial.map (algebraMap ℚ ℂ))).comp
        (Polynomial.X ^ (k - 1)) =
      ∏ Ω : Fin n → Fin (k - 1),
        Matrix.charpolyRev
          (Matrix.diagonal (fun i => MvPolynomial.C
              (Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) ^ (Ω i : ℕ))) *
            Matrix.of (fun i j : Fin n => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ))) := by
  sorry

end HararySachs.Hyper
