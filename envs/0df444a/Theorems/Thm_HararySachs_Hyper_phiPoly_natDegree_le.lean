-- Prove2me | Theorems.Thm_HararySachs_Hyper_phiPoly_natDegree_le
-- name    : HararySachs.Hyper.phiPoly_natDegree_le
-- status  : Open
-- author  : @milia
-- created : 2026-11-13T05:20:39.455928+00:00
-- url     : https://prove2.me/theorems/f5a5b3c7-3014-4ee6-9e41-ab9aa76731f3
-- title:
--   Degree bound for the z-polynomial of a resultant
-- statement:
--   Let $n \ge 1$, $k \ge 2$, $r = k-1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degree $r$ in $n$ variables (characterized by `IsResultant`). For any tensor $A$ with entries in a commutative ring $R$, let
--   $$\Phi_A(z) = \operatorname{Res}\bigl(x^{[r]} - z\,A x^{r}\bigr).$$
--   Then $\deg_z \Phi_A \le n\,r^{\,n-1}$.
--
--   Indeed, $\operatorname{Res}$ is homogeneous of degree $r^{n-1}$ in the coefficients of each of the $n$ equations, so every monomial of $\operatorname{Res}$ has total degree $n r^{n-1}$. Every coefficient of the system $x^{[r]} - zAx^r$ has degree at most $1$ in $z$.
--
--   **Formalization Note** $\Phi_A$ is `phiPoly A res` and the degree is `Polynomial.natDegree`.
-- source:
--   Homogeneity of the multivariate resultant; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and d6dcd7bc-30eb-4f12-bbe1-a5cdf67294f9.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- `Φ_A(z) = Res(x^{[r]} - z A x^r)` has degree at most `N = n r^{n-1}` in `z`. -/
theorem phiPoly_natDegree_le (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    {R : Type*} [CommRing R] (A : Fin n → (Fin (k - 1) → Fin n) → R) :
    (phiPoly (k := k) A res).natDegree ≤ n * (k - 1) ^ (n - 1) := by
  sorry

end HararySachs.Hyper
