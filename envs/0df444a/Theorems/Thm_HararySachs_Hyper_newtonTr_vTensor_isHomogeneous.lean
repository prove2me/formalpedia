-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_vTensor_isHomogeneous
-- name    : HararySachs.Hyper.newtonTr_vTensor_isHomogeneous
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T21:22:15.588199+00:00
-- url     : https://prove2.me/theorems/001a4a2b-d662-4c65-ae9b-19ea0e67bd5a
-- title:
--   The traces of the power system are homogeneous of degree $d(k-1)$
-- statement:
--   Let $n, k \ge 0$ and $r = k-1$, and let $\operatorname{Res}$ be any integer polynomial in the coefficients of $n$ forms of degree $r$ in $n$ variables. Let $V = (V_{ij})$ be an $n \times n$ matrix of indeterminates. Let $\tau_d(V) \in \mathbb{Q}[V]$ be the Newton traces of
--   $$\Phi_V(z) = \operatorname{Res}\bigl(x_1^{r} - z\,((Vx)_1)^{r},\ \dots,\ x_n^{r} - z\,((Vx)_n)^{r}\bigr),$$
--   given by $\tau_0 = 0$ and $\tau_d = -d\,\Phi_d - \sum_{j=1}^{d-1}\tau_j\,\Phi_{d-j}$. Then for every $d \ge 0$, the polynomial $\tau_d(V)$ is homogeneous of degree $d(k-1)$ in the entries of $V$.
--
--   This holds because the coefficient of $z^j$ in each equation is homogeneous of degree $j\,r$ in $V$. It is the grading fact behind the Morozov–Shakirov operator formula: an operator $\hat f_1^{a_1}\cdots\hat f_n^{a_n}$ of total order $r\,(a_1+\cdots+a_n)$ can have a nonzero constant term on $\tau_d(V)$ only when $a_1 + \cdots + a_n = d$.
--
--   **Formalization Note** No hypothesis on `res` is needed. The traces are `newtonTr (phiPoly (vTensor n k) res) d` in `AuxPoly n`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 4, proof of Proposition II (grading of $\log\det(I-A)$ by degree in $A$).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_vTensor_isHomogeneous (n k : ℕ)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (d : ℕ) :
    (newtonTr (phiPoly (k := k) (vTensor n k) res) d).IsHomogeneous (d * (k - 1)) := by sorry

end HararySachs.Hyper
