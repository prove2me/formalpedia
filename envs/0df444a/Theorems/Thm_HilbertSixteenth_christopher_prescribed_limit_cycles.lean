-- Prove2me | Theorems.Thm_HilbertSixteenth_christopher_prescribed_limit_cycles
-- name    : HilbertSixteenth.christopher_prescribed_limit_cycles
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:27:32.625092+00:00
-- url     : https://prove2.me/theorems/50b51c1e-2853-4774-95ec-75d0d73cdac2
-- title:
--   Theorem 2 (Christopher): prescribed algebraic limit cycles
-- statement:
--   Let $f=0$ be a non-singular real algebraic curve of degree $m$ (there is no point of $\mathbb R^2$ with $f=f_x=f_y=0$), and let $D$ be a polynomial of degree one such that the line $D=0$ does not meet the bounded components of $f=0$. Let $\alpha,\beta\in\mathbb R$ satisfy $\alpha D_x+\beta D_y\neq0$. Consider
--   $$\dot x=\alpha f - D f_y,\qquad \dot y = \beta f + D f_x.$$
--   Then this system has degree at most $m$, every bounded component of $f=0$ is a hyperbolic limit cycle of it, and it has no other limit cycles.
--
--   Applied to a union of circles, this gives a degree-$2n$ system realising any configuration of $n$ circles by algebraic limit cycles.
--
--   **Formalization Note** $D_x$ and $D_y$ are the coefficients of $x$ and $y$ in $D$. Non-singularity is required at real points, as in the survey. Hyperbolicity is encoded by a non-zero integral of the divergence over one period.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §6, Theorem 2 (C. Christopher, Geom. Dedicata 88 (2001) 255–258).

import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth
theorem christopher_prescribed_limit_cycles (f D : Poly2) (m : ℕ) (hf : f.totalDegree = m)
    (hsing : ∀ p : ℝ × ℝ, ¬ (evalAt f p = 0 ∧ evalAt (MvPolynomial.pderiv 0 f) p = 0 ∧
      evalAt (MvPolynomial.pderiv 1 f) p = 0))
    (hD : D.totalDegree = 1)
    (hline : ∀ C ∈ boundedComponents f, ∀ p ∈ C, evalAt D p ≠ 0)
    (α β : ℝ)
    (hαβ : α * MvPolynomial.coeff (Finsupp.single 0 1) D +
      β * MvPolynomial.coeff (Finsupp.single 1 1) D ≠ 0) :
    let V : PolyField :=
      ⟨MvPolynomial.C α * f - D * MvPolynomial.pderiv 1 f,
       MvPolynomial.C β * f + D * MvPolynomial.pderiv 0 f⟩
    V.degree ≤ m ∧
      (∀ C ∈ boundedComponents f, IsHyperbolicLimitCycle V.toField C) ∧
      ∀ O : Set (ℝ × ℝ), IsLimitCycle V.toField O → O ∈ boundedComponents f := by sorry
end HilbertSixteenth
