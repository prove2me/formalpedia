-- Prove2me | Theorems.Thm_MvResultant_blockDegree_ge
-- name    : MvResultant.blockDegree_ge
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T18:46:58.965584+00:00
-- url     : https://prove2.me/theorems/ed077c27-7638-4492-a9f8-d828595cdc5f
-- title:
--   Lower bound $\delta_i\ge\prod_{j\ne i}D_j$ for the block degrees of the resultant
-- statement:
--   Let $n\ge 1$ and $D_1,\dots,D_n\ge 0$. Let $\mathrm{Res}\in\mathbb{Z}[u_{i,\alpha}]$ be the multivariate resultant of $n$ homogeneous forms $F_i=\sum_{|\alpha|=D_i}u_{i,\alpha}x^\alpha$ in $n$ variables. It is characterised (`IsResultant`, following Hu–Huang–Ling–Qi, Definition 1.1) by three properties:
--   - it vanishes at the coefficients of $(F_1,\dots,F_n)$ over $\mathbb{C}$ if and only if the forms have a common nonzero zero;
--   - $\mathrm{Res}(x_1^{D_1},\dots,x_n^{D_n})=1$;
--   - it is irreducible over $\mathbb{C}$.
--
--   For $i\in[n]$, the *$i$-th block* is the set of coefficient variables $\{u_{i,\alpha}\}$ of the form $F_i$. A polynomial is *homogeneous of degree $\delta$ in block $i$* if every monomial in its support has total exponent $\delta$ in these variables (weighted homogeneity with weight $1$ on block $i$ and $0$ elsewhere).
--
--   **Statement.** Assume $D_j\ge1$ for all $j$. If $\mathrm{Res}$ is homogeneous of degree $\delta$ in block $i$, then
--   $$\prod_{j\ne i}D_j\;\le\;\delta.$$
--
--   Expected proof, by specialisation. Fix $F_j=x_j^{D_j}-x_i^{D_j}$ for $j\ne i$. Their common projective zeros are the $M=\prod_{j\ne i}D_j$ distinct points with $x_i=1$ and each $x_j$ a $D_j$-th root of unity. Restricted to these forms, $\mathrm{Res}$ becomes a polynomial $r$ in the coefficients of $F_i$, which is homogeneous of degree $\delta$. It vanishes on each hyperplane $\{F_i(p_l)=0\}$, so it is divisible by $M$ pairwise non-associate linear forms. It is nonzero: at $F_i=x_i^{D_i}$ there is no common zero. Hence $\delta=\deg r\ge M$.
-- source:
--   Gelfand–Kapranov–Zelevinsky, Discriminants, Resultants and Multidimensional Determinants, Ch. 13, Prop. 13.1.1; Cox–Little–O'Shea, Using Algebraic Geometry, Ch. 3.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem blockDegree_ge {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) (δ : ℕ)
    (hδ : res.IsWeightedHomogeneous (fun v : ResVar n D => if v.1 = i then 1 else 0) δ) :
    ∏ j ∈ Finset.univ.erase i, D j ≤ δ := by sorry

end MvResultant
