-- Prove2me | Theorems.Thm_HararySachs_Hyper_charPoly_coeff_of_blockHomogeneous
-- name    : HararySachs.Hyper.charPoly_coeff_of_blockHomogeneous
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T18:46:57.26777+00:00
-- url     : https://prove2.me/theorems/c82b86c7-08bd-41d7-b6fb-a4b4018bdc61
-- title:
--   Leading coefficient of $\varphi_H$ from block-homogeneity and normalisation of the resultant
-- statement:
--   Let $H$ be a hypergraph on $n$ vertices with edge set $E$ and let $k\ge1$. Let $R\in\mathbb{Z}[u_{i,\alpha}]$ be any polynomial in the coefficients $u_{i,\alpha}$ ($|\alpha|=k-1$) of $n$ forms of degree $k-1$. Assume:
--   - **block-homogeneity:** $R$ is homogeneous of the same degree $\delta$ in each block $\{u_{i,\alpha}\}_\alpha$, $i=1,\dots,n$;
--   - **normalisation:** $R(x_1^{k-1},\dots,x_n^{k-1})=1$.
--
--   Let $\varphi_H(\lambda)$ be obtained by substituting into $R$ the coefficients of $\lambda x_i^{k-1}-(\mathcal{A}x^{k-1})_i$, as in `charPoly`. Then
--   $$[\lambda^{n\delta}]\,\varphi_H(\lambda)=1.$$
--
--   This is pure algebra. Every monomial of $R$ has total degree $n\delta$. Each substituted coefficient has the form $b+\lambda e$, where $e=1$ for the diagonal monomial $x_i^{k-1}$ and $e=0$ otherwise. So the coefficient of $\lambda^{n\delta}$ is $R(e)=R(x_1^{k-1},\dots,x_n^{k-1})=1$.
--
--   Combined with $\delta=(k-1)^{n-1}$ for the resultant, this gives `charPoly_coeff_top`.
-- source:
--   Hu–Huang–Ling–Qi, J. Symbolic Comput. 50 (2013), Theorem 2.3 and Proposition 2.4; Cooper–Dutle, Spectra of uniform hypergraphs, Linear Algebra Appl. 436 (2012), Section 2.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

namespace HararySachs.Hyper

theorem charPoly_coeff_of_blockHomogeneous (n k : ℕ) (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (δ : ℕ)
    (hδ : ∀ i : Fin n, res.IsWeightedHomogeneous
      (fun v : ResVar n (fun _ => k - 1) => if v.1 = i then 1 else 0) δ)
    (hnorm : MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
      if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0) res = 1) :
    (charPoly (k := k) E res).coeff (n * δ) = 1 := by sorry

end HararySachs.Hyper
