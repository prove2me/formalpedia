-- Prove2me | Theorems.Thm_MvResultant_dvd_of_vanishing
-- name    : MvResultant.dvd_of_vanishing
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T18:57:15.783948+00:00
-- url     : https://prove2.me/theorems/a80b6b23-73d5-4996-aadf-eb653f4e61b1
-- title:
--   Polynomials vanishing on the resultant locus are divisible by the resultant
-- statement:
--   Let $n\ge 1$ and $D_1,\dots,D_n\ge 0$. Let $\mathrm{Res}\in\mathbb{Z}[u_{i,\alpha}]$ be the multivariate resultant of $n$ homogeneous forms $F_i=\sum_{|\alpha|=D_i}u_{i,\alpha}x^\alpha$ in $n$ variables. It is characterised (`IsResultant`, following Hu–Huang–Ling–Qi, Definition 1.1) by three properties:
--   - it vanishes at the coefficients of $(F_1,\dots,F_n)$ over $\mathbb{C}$ if and only if the forms have a common nonzero zero;
--   - $\mathrm{Res}(x_1^{D_1},\dots,x_n^{D_n})=1$;
--   - it is irreducible over $\mathbb{C}$.
--
--   **Statement.** Let $g\in\mathbb{C}[u_{i,\alpha}]$ vanish at the coefficient vector of every system $(F_1,\dots,F_n)$ of forms of degrees $D_1,\dots,D_n$ that has a common nonzero zero in $\mathbb{C}^n$. Then $\mathrm{Res}$, viewed over $\mathbb{C}$, divides $g$.
--
--   This follows from Hilbert's Nullstellensatz. The variables $u_{i,\alpha}$ are finitely many. By the first property, the vanishing locus of $\mathrm{Res}$ is exactly the set of solvable systems, so $g$ lies in the vanishing ideal of $V(\mathrm{Res})$, which is $\sqrt{(\mathrm{Res})}$. Since $\mathrm{Res}$ is irreducible in the UFD $\mathbb{C}[u]$, the ideal $(\mathrm{Res})$ is prime, hence radical.
--
--   This is the basic tool for deriving properties of $\mathrm{Res}$ from its characterisation alone: block-homogeneity, the degree bounds, uniqueness, and Poisson-type formulas.
-- source:
--   Hilbert's Nullstellensatz; resultant characterisation of Hu–Huang–Ling–Qi, J. Symbolic Comput. 50 (2013), Definition 1.1 (after Cox–Little–O'Shea, Using Algebraic Geometry, Ch. 3, Thm 2.3); Gelfand–Kapranov–Zelevinsky, Discriminants, Resultants and Multidimensional Determinants, Ch. 13.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem dvd_of_vanishing {n : ℕ} {D : Fin n → ℕ}
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res)
    (g : MvPolynomial (ResVar n D) ℂ)
    (hg : ∀ F : Fin n → MvPolynomial (Fin n) ℂ, (∀ i, (F i).IsHomogeneous (D i)) →
      (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (F i) = 0) →
      MvPolynomial.aeval (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (F v.1)) g = 0) :
    MvPolynomial.map (Int.castRingHom ℂ) res ∣ g := by sorry

end MvResultant
