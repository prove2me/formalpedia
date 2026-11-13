-- Prove2me | Theorems.Thm_HararySachs_Hyper_codegCoeff_eq_phiPoly
-- name    : HararySachs.Hyper.codegCoeff_eq_phiPoly
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T20:25:39.108557+00:00
-- url     : https://prove2.me/theorems/83bc614f-34e3-4cf2-b873-e3c1fb9da3c4
-- title:
--   Rescaling $\varphi_H(\lambda)=\lambda^{N}\Phi(1/\lambda)$: codegree coefficients as coefficients of $\Phi$
-- statement:
--   Let $n \ge 1$ and $k \ge 2$, and let $E$ be a family of subsets of $\{1,\dots,n\}$ with adjacency tensor $\mathcal{A}$, where $a_{i_1\cdots i_k} = 1/(k-1)!$ if $\{i_1,\dots,i_k\} \in E$ and $0$ otherwise. Let $\operatorname{Res}$ be the resultant of $n$ forms of degree $k-1$ in $n$ variables, normalized by $\operatorname{Res}(x_1^{k-1},\dots,x_n^{k-1}) = 1$. Put $N = n(k-1)^{n-1}$ and consider
--   $$\varphi_H(\lambda) = \operatorname{Res}\bigl(\lambda x^{[k-1]} - \mathcal{A}x^{k-1}\bigr), \qquad \Phi(z) = \operatorname{Res}\bigl(x^{[k-1]} - z\,\mathcal{A}x^{k-1}\bigr).$$
--   Then for every $0 \le d \le N$,
--   $$[\lambda^{N-d}]\,\varphi_H(\lambda) = [z^{d}]\,\Phi(z).$$
--
--   In other words $\varphi_H(\lambda) = \lambda^{N}\,\Phi(1/\lambda)$, because the resultant is homogeneous of total degree $N$ in the coefficients. This moves the codegree coefficients of the characteristic polynomial to the low-order coefficients of a polynomial with constant term $1$, where logarithms and Newton identities are taken.
--
--   **Formalization Note** The left side is `codegCoeff E res d`. The right side is the $d$-th coefficient of `phiPoly` applied to the tensor $(i,t) \mapsto$ `adjEntry E (Fin.cons i t)`.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 3, Theorem 3 and Definition 1 (the characteristic polynomial as a resultant); Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 4 (the normalization $\operatorname{Res}(I - f)$).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem codegCoeff_eq_phiPoly (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (d : ℕ) (hd : d ≤ n * (k - 1) ^ (n - 1)) :
    codegCoeff (k := k) E res d =
      (phiPoly (R := ℚ) (k := k) (fun i t => adjEntry E (Fin.cons i t)) res).coeff d := by sorry

end HararySachs.Hyper
