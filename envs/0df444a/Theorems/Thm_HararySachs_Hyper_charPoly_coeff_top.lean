-- Prove2me | Theorems.Thm_HararySachs_Hyper_charPoly_coeff_top
-- name    : HararySachs.Hyper.charPoly_coeff_top
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T05:16:51.908964+00:00
-- url     : https://prove2.me/theorems/20aadd2a-84c1-4192-9d1e-84ad302cdcb2
-- title:
--   The characteristic polynomial of a $k$-graph is monic of degree $n(k-1)^{n-1}$ (leading coefficient)
-- statement:
--   Let $H$ be a $k$-uniform hypergraph on $n \ge 1$ vertices with $k \ge 2$, with edge set $E$, and let $\mathcal{A}$ be its normalized adjacency hypermatrix. Let $\operatorname{Res}$ be the multivariate resultant of $n$ homogeneous forms of degree $k-1$ in $n$ variables. It is characterised by three properties:
--   - it vanishes exactly when the forms have a common nontrivial zero over $\mathbb{C}$;
--   - it is normalized to $1$ on $(x_1^{k-1}, \dots, x_n^{k-1})$;
--   - it is irreducible.
--
--   The characteristic polynomial is
--   $$\varphi_H(\lambda) = \operatorname{Res}\big(\lambda x_i^{k-1} - (\mathcal{A}x^{k-1})_i\big)_{i=1}^n.$$
--   Its coefficient of $\lambda^{N}$, where $N = n(k-1)^{n-1}$, equals $1$.
--
--   Together with $\deg \varphi_H = N$, this is the statement that $\varphi_H$ is monic of degree $n(k-1)^{n-1}$. It follows from the homogeneity of the resultant (degree $(k-1)^{n-1}$ in the coefficients of each form) and its normalization, since $\lambda$ enters only through the diagonal coefficients. (Edges have at least two vertices, so $\mathcal{A}$ has no diagonal entries.) This fixes the constant term $c_0 = 1$ in the Newton recursion for the codegree coefficients.
-- source:
--   Cooper–Dutle, Spectra of uniform hypergraphs, Linear Algebra Appl. 436 (2012), Section 2 (degree $n(k-1)^{n-1}$ of the characteristic polynomial); Clark–Cooper, arXiv:1812.00468v2, Section 2.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

namespace HararySachs.Hyper

theorem charPoly_coeff_top (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    (charPoly (k := k) E res).coeff (n * (k - 1) ^ (n - 1)) = 1 := by sorry

end HararySachs.Hyper
