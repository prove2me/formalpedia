-- Prove2me | Theorems.Thm_MvResultant_blockDegree_le
-- name    : MvResultant.blockDegree_le
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T18:46:54.637847+00:00
-- url     : https://prove2.me/theorems/d7c662fc-6e38-4eca-a560-e20b2a53f659
-- title:
--   Upper bound $\delta_i\le\prod_{j\ne i}D_j$ for the block degrees of the resultant
-- statement:
--   Let $n\ge 1$ and $D_1,\dots,D_n\ge 0$. Let $\mathrm{Res}\in\mathbb{Z}[u_{i,\alpha}]$ be the multivariate resultant of $n$ homogeneous forms $F_i=\sum_{|\alpha|=D_i}u_{i,\alpha}x^\alpha$ in $n$ variables. It is characterised (`IsResultant`, following Hu–Huang–Ling–Qi, Definition 1.1) by three properties:
--   - it vanishes at the coefficients of $(F_1,\dots,F_n)$ over $\mathbb{C}$ if and only if the forms have a common nonzero zero;
--   - $\mathrm{Res}(x_1^{D_1},\dots,x_n^{D_n})=1$;
--   - it is irreducible over $\mathbb{C}$.
--
--   For $i\in[n]$, the *$i$-th block* is the set of coefficient variables $\{u_{i,\alpha}\}$ of the form $F_i$. A polynomial is *homogeneous of degree $\delta$ in block $i$* if every monomial in its support has total exponent $\delta$ in these variables (weighted homogeneity with weight $1$ on block $i$ and $0$ elsewhere).
--
--   **Statement.** Assume $D_j\ge1$ for all $j$. If $\mathrm{Res}$ is homogeneous of degree $\delta$ in block $i$, then
--   $$\delta\;\le\;\prod_{j\ne i}D_j.$$
--
--   Expected proof, via the Macaulay determinant. Put $D=\sum_j(D_j-1)+1$, and build the square Macaulay matrix $M$ indexed by the monomials of degree $D$:
--   - each row monomial $x^\beta$ is assigned to the first form $F_j$ with $x_j^{D_j}\mid x^\beta$, with the form $i$ placed last in the order;
--   - the row lists the coefficients of $(x^\beta/x_j^{D_j})\,F_j$.
--
--   Then:
--   - $\det M$ vanishes on every solvable system, since the monomial vector of a common zero lies in its kernel;
--   - $\det M=1$ on the diagonal system, so $\det M\neq0$;
--   - the rows assigned to $F_i$ are linear in block $i$, and there are exactly $\prod_{j\ne i}D_j$ of them.
--
--   By *Divisibility from the Nullstellensatz:* every polynomial vanishing at all solvable systems is divisible by $\mathrm{Res}$. This holds because the vanishing locus of $\mathrm{Res}$ is the set of solvable systems, and $(\mathrm{Res})$ is prime, hence radical, since $\mathrm{Res}$ is irreducible. So $\mathrm{Res}\mid\det M$, which gives the bound.
-- source:
--   F. S. Macaulay, Some formulae in elimination, Proc. London Math. Soc. 35 (1902); Cox–Little–O'Shea, Using Algebraic Geometry, Ch. 3 §4; Gelfand–Kapranov–Zelevinsky, Ch. 13, Prop. 13.1.1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem blockDegree_le {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) (δ : ℕ)
    (hδ : res.IsWeightedHomogeneous (fun v : ResVar n D => if v.1 = i then 1 else 0) δ) :
    δ ≤ ∏ j ∈ Finset.univ.erase i, D j := by sorry

end MvResultant
