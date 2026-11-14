-- Prove2me | Theorems.Thm_HararySachs_Hyper_phiPoly_vTensor_eval
-- name    : HararySachs.Hyper.phiPoly_vTensor_eval
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T05:20:43.809011+00:00
-- url     : https://prove2.me/theorems/b301432a-8e6b-4336-88e2-9ae2c5623822
-- title:
--   Evaluating the power-system resultant at a matrix
-- statement:
--   Let $r = k-1$ and let $\Phi_V(z) = \operatorname{Res}\bigl(x_i^r - z\,(Vx)_i^r\bigr)$ be the resultant of the power system with matrix of indeterminates $V$ (`phiPoly (vTensor n k) res`). Map its coefficients to $\mathbb{C}$, set $z = 1$, and evaluate at a complex matrix $M$. The result equals the resultant (`res`, evaluated through the coefficients) of the system of forms
--   $$F_i(x) = x_i^{r} - \Bigl(\sum_j M_{ij}\,x_j\Bigr)^{r}, \qquad i = 1,\dots,n.$$
--   No hypothesis on `res` is needed: both sides are the same polynomial evaluated at the same coefficients.
--
--   **Formalization Note** The matrix $M$ is given as `x : Fin n × Fin n → ℂ` with $M_{ij} = x(i,j)$. The resultant of $F$ is `MvPolynomial.aeval (fun v => coeff v.2.1 (F v.1)) (map (Int.castRingHom ℂ) res)`.
-- source:
--   Definitional bookkeeping for the power system; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and d6dcd7bc-30eb-4f12-bbe1-a5cdf67294f9.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- Evaluating `Φ_V(1)` at a complex matrix `M` gives the resultant of the power system
`x_i^r - (M x)_i^r`. -/
theorem phiPoly_vTensor_eval (n k : ℕ) (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (x : Fin n × Fin n → ℂ) :
    MvPolynomial.eval x
        (((phiPoly (k := k) (vTensor n k) res).map
          (MvPolynomial.map (algebraMap ℚ ℂ))).eval 1) =
      MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
          MvPolynomial.coeff v.2.1
            ((MvPolynomial.X v.1 ^ (k - 1) -
              (∑ j, MvPolynomial.C (x (v.1, j)) * MvPolynomial.X j) ^ (k - 1) :
                MvPolynomial (Fin n) ℂ)))
        (MvPolynomial.map (Int.castRingHom ℂ) res) := by
  sorry

end HararySachs.Hyper
