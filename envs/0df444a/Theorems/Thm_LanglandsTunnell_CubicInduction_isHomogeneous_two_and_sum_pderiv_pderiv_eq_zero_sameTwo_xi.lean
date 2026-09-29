-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi
-- name    : LanglandsTunnell.CubicInduction.isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/29a47933-4039-5e19-9769-c9499ac561b5
-- title:
--   Degree-two same-degree transition polynomial is harmonic
-- statement:
--   Let $\nu \in \mathbb{C}^3$ and let $p \in \mathbb{C}[x_0,x_1,x_2]$ be homogeneous of degree $2$ with $\sum_{i} \partial_i^2 p = 0$. Two auxiliary operations are introduced in the statement. First, $\Xi$ assigns to a triple $\nu$ and a polynomial $p$ the $3\times 3$ matrix over $\mathbb{C}[x_0,x_1,x_2]$ whose diagonal entry in position $c$ is $2(\nu_c + \varepsilon_c)\,p$, where $\varepsilon = (1,0,-1)$, and whose entry in an off-diagonal position $(c,d)$ is $-\bigl(x_{\max(c,d)}\,\partial_{\min(c,d)}p - x_{\min(c,d)}\,\partial_{\max(c,d)}p\bigr)$. Second, for a matrix $M$ of polynomials, writing $E(M) = \sum_{c,d} x_c\,\partial_d M_{cd}$, $r^2 = \sum_i x_i^2$ and $\Delta = \sum_i \partial_i^2$, one sets $\mathrm{same}_2(M) = 6\,E(M) - r^2\,\Delta E(M)$. The conclusion is that $\mathrm{same}_2(\Xi(\nu,p))$ is homogeneous of degree $2$ and satisfies $\Delta\,\mathrm{same}_2(\Xi(\nu,p)) = 0$.
--
--   The polynomial $\mathrm{same}_2(M)$ is six times the harmonic projection of the Euler contraction $E(M)$ of the matrix $M$, and the assertion is the degree-two same-degree clause needed when one checks that a family of polynomial data is stable under the transition operators. It is cited in the construction of transition-stable families on a sign-isotypic submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi
    (ν : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 2)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    (same₂ (Ξ ν p)).IsHomogeneous 2 ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (same₂ (Ξ ν p)))) = 0 := by sorry
