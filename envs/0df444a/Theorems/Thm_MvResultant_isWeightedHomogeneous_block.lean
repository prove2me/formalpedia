-- Prove2me | Theorems.Thm_MvResultant_isWeightedHomogeneous_block
-- name    : MvResultant.isWeightedHomogeneous_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T18:47:05.118303+00:00
-- url     : https://prove2.me/theorems/47d4ad9f-b658-42f7-ad72-5a3bb867485f
-- title:
--   The resultant is homogeneous in the coefficients of each form
-- statement:
--   Let $n\ge 1$ and $D_1,\dots,D_n\ge 0$. Let $\mathrm{Res}\in\mathbb{Z}[u_{i,\alpha}]$ be the multivariate resultant of $n$ homogeneous forms $F_i=\sum_{|\alpha|=D_i}u_{i,\alpha}x^\alpha$ in $n$ variables. It is characterised (`IsResultant`, following Hu–Huang–Ling–Qi, Definition 1.1) by three properties:
--   - it vanishes at the coefficients of $(F_1,\dots,F_n)$ over $\mathbb{C}$ if and only if the forms have a common nonzero zero;
--   - $\mathrm{Res}(x_1^{D_1},\dots,x_n^{D_n})=1$;
--   - it is irreducible over $\mathbb{C}$.
--
--   For $i\in[n]$, the *$i$-th block* is the set of coefficient variables $\{u_{i,\alpha}\}$ of the form $F_i$. A polynomial is *homogeneous of degree $\delta$ in block $i$* if every monomial in its support has total exponent $\delta$ in these variables (weighted homogeneity with weight $1$ on block $i$ and $0$ elsewhere).
--
--   **Statement.** For every $i\in[n]$ there is $\delta_i\in\mathbb{N}$ such that $\mathrm{Res}$ is homogeneous of degree $\delta_i$ in block $i$.
--
--   Expected proof: scaling $F_i\mapsto cF_i$ with $c\neq0$ does not change the common zeros. By *Divisibility from the Nullstellensatz:* every polynomial vanishing at all solvable systems is divisible by $\mathrm{Res}$. This holds because the vanishing locus of $\mathrm{Res}$ is the set of solvable systems, and $(\mathrm{Res})$ is prime, hence radical, since $\mathrm{Res}$ is irreducible. Hence $\mathrm{Res}(\dots,cF_i,\dots)=\mu(c)\,\mathrm{Res}$ for a constant $\mu(c)$. Comparing the block-$i$ homogeneous components $r_d$ gives $c^d r_d=\mu(c)\,r_d$, so taking $c=2$ shows that at most one $r_d$ is nonzero.
--
--   The actual degree is $\delta_i=\prod_{j\ne i}D_j$, which is proved in the two companion bounds `MvResultant.blockDegree_le` and `MvResultant.blockDegree_ge`.
-- source:
--   Gelfand–Kapranov–Zelevinsky, Discriminants, Resultants and Multidimensional Determinants, Ch. 13, Prop. 13.1.1; Hu–Huang–Ling–Qi, J. Symbolic Comput. 50 (2013), Proposition 2.4.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem isWeightedHomogeneous_block {n : ℕ} {D : Fin n → ℕ}
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) :
    ∃ δ : ℕ, res.IsWeightedHomogeneous
      (fun v : ResVar n D => if v.1 = i then 1 else 0) δ := by sorry

end MvResultant
