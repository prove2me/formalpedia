-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
-- name    : LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/008c90bd-633d-5c23-b87d-454ed2fd1318
-- title:
--   Induced-picture operators commute with multiplication by det X
-- statement:
--   Fix a triple of complex numbers $\nu = (\nu_0,\nu_1,\nu_2)$, two indices $c,d \in \{0,1,2\}$, and a polynomial $P$ in the nine commuting variables $X_{(i,j)}$, $i,j \in \{0,1,2\}$, over $\mathbb{C}$. The statement introduces, by a local definition, the operator $\mathrm{act}\,\nu\,c\,d$ on $\mathbb{C}[X_{(i,j)}]$ given as the sum of two terms: a multiplication operator, multiplication by $\sum_{a} (\nu_a + \rho_a)\, X_{(a,c)} X_{(a,d)}$ with the constants $\rho = (1,0,-1)$ inserted through `MvPolynomial.C`; and a first-order term $\sum_{i}\sum_{j} \bigl(\sum_{m} \kappa_{i m} X_{(m,j)}\bigr)\, \partial P/\partial X_{(i,j)}$, where the coefficients $\kappa_{i m}$ are $X_{(i,c)} X_{(m,d)}$ when $m < i$, $-X_{(m,c)} X_{(i,d)}$ when $i < m$, and $0$ when $m = i$, and $\partial/\partial X_{(i,j)}$ is `MvPolynomial.pderiv`. Writing $D$ for the determinant of the generic matrix $\mathrm{Matrix.of}\,(i,j) \mapsto X_{(i,j)}$, the conclusion is the polynomial identity $\mathrm{act}\,\nu\,c\,d\,(D \cdot P) = D \cdot \mathrm{act}\,\nu\,c\,d\,(P)$, valid for all $\nu$, all $c,d$ and all $P$.
--
--   The content is that the derivation part of $\mathrm{act}\,\nu\,c\,d$ is differentiation along the vector field $X \mapsto \kappa X$ with $\kappa$ antisymmetric, so by Jacobi's formula for the derivative of a determinant it annihilates $\det X$, while the remaining part of the operator is a multiplication operator; the identity therefore lets determinant twists $\det(X)^{\alpha}$ be moved through the induced-picture action. It is used in the cubic-induction analysis within the Langlands–Tunnell input, for instance by the lemmas on evaluating the rotation Casimir on $\det^{\,n} \cdot P$ for harmonic $P$, on reading off sign-isotypic vectors, and on vanishing over separating stable submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    act ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * act ν c d P := by sorry
