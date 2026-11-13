-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_vTensor
-- name    : HararySachs.Hyper.newtonTr_vTensor
-- status  : Open
-- author  : @milia
-- created : 2026-11-12T20:26:08.458205+00:00
-- url     : https://prove2.me/theorems/bbec97f7-5a73-441a-8c86-f56e7ba70cf9
-- title:
--   Traces of the power system $x_i^{k-1} = ((Vx)_i)^{k-1}$
-- statement:
--   Let $n \ge 1$, $k \ge 2$ and $r = k-1$, and let $\operatorname{Res}$ be the normalized resultant of $n$ forms of degree $r$ in $n$ variables. Let $V = (V_{ij})$ be an $n \times n$ matrix of indeterminates, and let $\tau_d(V) \in \mathbb{Q}[V]$ be the Newton traces of
--   $$\Phi_V(z) = \operatorname{Res}\bigl(x_1^{r} - z\,((Vx)_1)^{r},\ \dots,\ x_n^{r} - z\,((Vx)_n)^{r}\bigr),$$
--   so that $\log \Phi_V(z) = -\sum_{d \ge 1} \tau_d(V)\, z^{d}/d$. For a rational tensor $A$, let $\hat f_i = \sum_t A_{i,t}\,\partial_{V_{i t_1}}\cdots\partial_{V_{i t_r}}$ as in Equation (1) of the source. Then for every $d \ge 1$ and every $a \in \mathbb{N}^n$ with $a_1+\cdots+a_n = d$,
--   $$\Bigl[\hat f_1^{a_1}\cdots\hat f_n^{a_n}\,\tau_d(V)\Bigr]_{V=0} = (k-1)^{n-1}\,\Bigl[\hat f_1^{a_1}\cdots\hat f_n^{a_n}\,\operatorname{tr}\bigl(V^{d(k-1)}\bigr)\Bigr]_{V=0}.$$
--
--   Equivalently, $\tau_d(V)$ and $(k-1)^{n-1}\operatorname{tr}(V^{d(k-1)})$ have the same coefficients on all monomials whose row degrees are $(r a_1,\dots,r a_n)$. This is the base case of the Morozov–Shakirov identity. For the power system, the resultant becomes a product of determinants, and the identity reduces to $\log\det = \operatorname{tr}\log$. Combined with the generalized Proposition II, it identifies the Newton traces of $\Phi$ with the Morozov–Shakirov traces $\mathrm{Tr}_d$ of Equation (1).
--
--   **Formalization Note** $\tau_d(V)$ is `newtonTr (phiPoly (vTensor n k) res) d`, the bracket is `MvPolynomial.coeff 0`, the operator product is `tapplyAll A a`, and $\operatorname{tr}(V^{L})$ is `trPow n L`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 4, the final step of the proof of Proposition II (reduction to $\log\det(I-A) = \operatorname{tr}\log(I-A)$); Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 4, Equation (1).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_vTensor (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (d : ℕ) (hd : 1 ≤ d)
    (a : Fin n → Fin (d + 1)) (ha : (∑ i, (a i).val) = d) :
    MvPolynomial.coeff 0
        (tapplyAll (k := k) A a (newtonTr (phiPoly (k := k) (vTensor n k) res) d)) =
      ((k - 1 : ℕ) : ℚ) ^ (n - 1) *
        MvPolynomial.coeff 0 (tapplyAll (k := k) A a (trPow n (d * (k - 1)))) := by sorry

end HararySachs.Hyper
