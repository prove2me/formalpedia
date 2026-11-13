-- Prove2me | Theorems.Thm_MvResultant_poisson_block
-- name    : MvResultant.poisson_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:02:03.508849+00:00
-- url     : https://prove2.me/theorems/5d9325ae-58b4-4577-9fc0-829df265f803
-- title:
--   Poisson product formula in one block
-- statement:
--   Let $D_1,\dots,D_n \ge 1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degrees $D_1,\dots,D_n$ in $n$ variables. Here it is characterized by: vanishing exactly at systems with a nontrivial common zero, the normalization $\operatorname{Res}(x_1^{D_1},\dots,x_n^{D_n}) = 1$, and irreducibility. Fix $i$ and forms $F_j$ of degree $D_j$ for $j \ne i$. Suppose $P$ is a set of $\prod_{j \ne i} D_j$ points $p \in \mathbb{C}^n$, each with $p_i = 1$ and $F_j(p) = 0$ for all $j \ne i$. Then for every form $\varphi$ of degree $D_i$,
--   $$\operatorname{Res}\bigl(\varphi \text{ in place } i,\ F_j \text{ for } j\ne i\bigr) = \operatorname{Res}\bigl(x_i^{D_i} \text{ in place } i,\ F_j\bigr)\cdot\prod_{p \in P}\varphi(p).$$
--
--   This is Poisson's formula in the case where the other equations are in general position, with the multiplicities settled by the exact block degree of the resultant. It expresses the dependence of the resultant on one equation through the values of that equation at the common zeros of the others.
--
--   **Formalization Note** The system with $\varphi$ in place $i$ is `Function.update F i φ`. The resultant is evaluated through `MvPolynomial.aeval` of the coefficients of the system.
-- source:
--   Poisson product formula for resultants; Cox, Little, O'Shea, Using Algebraic Geometry, 2nd ed., Ch. 3, §3, Theorem 3.4; Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem poisson_block {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n)
    (F : Fin n → MvPolynomial (Fin n) ℂ) (hF : ∀ j, j ≠ i → (F j).IsHomogeneous (D j))
    (P : Finset (Fin n → ℂ)) (hcard : P.card = ∏ j ∈ Finset.univ.erase i, D j)
    (hP : ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i → MvPolynomial.eval p (F j) = 0)
    (φ : MvPolynomial (Fin n) ℂ) (hφ : φ.IsHomogeneous (D i)) :
    MvPolynomial.aeval
        (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (Function.update F i φ v.1))
        (MvPolynomial.map (Int.castRingHom ℂ) res) =
      MvPolynomial.aeval (fun v : ResVar n D =>
          MvPolynomial.coeff v.2.1 (Function.update F i (MvPolynomial.X i ^ D i) v.1))
        (MvPolynomial.map (Int.castRingHom ℂ) res) *
      ∏ p ∈ P, MvPolynomial.eval p φ := by sorry

end MvResultant
