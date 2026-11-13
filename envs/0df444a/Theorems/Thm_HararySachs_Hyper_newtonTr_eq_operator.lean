-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_eq_operator
-- name    : HararySachs.Hyper.newtonTr_eq_operator
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T20:25:33.808846+00:00
-- url     : https://prove2.me/theorems/5ccc7c3c-0ec8-45f2-9559-8cc18a006ba3
-- title:
--   Generalized Morozov–Shakirov Proposition II, degree-preserving form
-- statement:
--   Let $n \ge 1$, $k \ge 2$ and $r = k-1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degree $r$ in $n$ variables, normalized by $\operatorname{Res}(x_1^{r},\dots,x_n^{r}) = 1$. For a tensor $A$ with rational entries $A_{i,t}$ ($i \in \{1,\dots,n\}$, $t \in \{1,\dots,n\}^r$), let $\tau_d(A)$ be the Newton traces of
--   $$\Phi_A(z) = \operatorname{Res}\bigl(x^{[r]} - z\,\mathcal{A}x^{r}\bigr), \qquad\text{so that}\qquad \log \Phi_A(z) = -\sum_{d \ge 1} \frac{\tau_d(A)}{d}\, z^{d}.$$
--   Let $V = (V_{ij})$ be an $n \times n$ matrix of indeterminates, and let $\tau_d(V) \in \mathbb{Q}[V]$ be the Newton traces of $\operatorname{Res}\bigl(x^{[r]} - z\,((Vx)_i^{r})_i\bigr)$, the resultant of the power system $x_i^{r} = z\,((Vx)_i)^{r}$. Write
--   $$\hat f_i = \sum_{t} A_{i,t}\,\frac{\partial}{\partial V_{i t_1}}\cdots\frac{\partial}{\partial V_{i t_r}}.$$
--   Then for every $d \ge 1$,
--   $$\tau_d(A) = \sum_{\substack{a \in \mathbb{N}^n \\ a_1+\cdots+a_n = d}} \frac{1}{\prod_{i} (r a_i)!}\, \Bigl[\hat f_1^{a_1}\cdots\hat f_n^{a_n}\,\tau_d(V)\Bigr]_{V=0}.$$
--
--   This is the coefficient form of the generalized $\log\det = \operatorname{tr}\log$ identity of Morozov and Shakirov (Proposition II). It expresses the logarithm of the resultant of an arbitrary system through the resultant of the power system $x_i^{r} = ((Vx)_i)^{r}$. Unlike the source, every resultant involved has degrees $(r,\dots,r)$: the linear equation $x_1 - v\cdot x$ used there is replaced by $x_1^{r} - (v\cdot x)^{r}$, so the statement only needs the single resultant `res`.
--
--   **Formalization Note** $\tau_d$ is `newtonTr` of `phiPoly`, and the power tensor is `vTensor n k`. The tuple $a$ ranges over `Fin n → Fin (d + 1)` with $\sum_i a_i = d$. The bracket $[\,\cdot\,]_{V=0}$ is `MvPolynomial.coeff 0`, and the operator product is `tapplyAll A a`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 4, Proposition II and eq. (16), in the variant that replaces the linear equation $x_1 - v\cdot x$ by $x_1^{k-1} - (v\cdot x)^{k-1}$ (mission strategy comment 2173f2a9-fd2e-4d5e-afb5-27607d970161).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_eq_operator (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k) A res) d =
      ∑ a : Fin n → Fin (d + 1),
        if (∑ i, (a i).val) = d then
          MvPolynomial.coeff 0
              (tapplyAll (k := k) A a (newtonTr (phiPoly (k := k) (vTensor n k) res) d)) /
            ∏ i, (Nat.factorial ((a i).val * (k - 1)) : ℚ)
        else 0 := by sorry

end HararySachs.Hyper
