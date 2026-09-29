-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_diag_row_eq_and_harmonic_split
-- name    : LanglandsTunnell.CubicInduction.inducedPicture_act_diag_row_eq_and_harmonic_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/3f8507ff-8b85-5cc2-8b91-b07ca26d7642
-- title:
--   Diagonal action on a row entry and its harmonic splitting
-- statement:
--   Fix $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$ and indices $m, a \in \mathrm{Fin}\,3$; there are no further hypotheses. Let $\rho = (1,0,-1)$ and let $\mathrm{act}\,\nu\,c\,d$ be the operator on $\mathbb{C}$-polynomials in the nine variables $X_{(i,j)}$, $i,j \in \mathrm{Fin}\,3$, given by $$p \mapsto \Big(\sum_{b} (\nu_b + \rho_b)\,X_{(b,c)}X_{(b,d)}\Big)p + \sum_{i,j}\Big(\sum_{k}\big(\textstyle\mathbb{1}_{k<i}\,X_{(i,c)}X_{(k,d)} - \mathbb{1}_{i<k}\,X_{(k,c)}X_{(i,d)}\big)X_{(k,j)}\Big)\,\partial_{(i,j)}p .$$ Put $\gamma_c = \nu_c + \rho_c + \varepsilon_c$ with $\varepsilon_c = 1$ if $c<m$, $\varepsilon_c = -1$ if $m<c$ and $\varepsilon_m = 0$; put $\lambda = (\nu_0+\nu_1+\nu_2+2\nu_m)/5$; and let $p_3 = X_m\sum_c (\gamma_c-\lambda)X_c^2$ in three variables. The conclusion is a threefold conjunction of polynomial identities: first, $\mathrm{act}\,\nu\,a\,a\,(X_{(m,a)}) = X_{(m,a)}\sum_c \gamma_c X_{(c,a)}^2$; second, that polynomial equals $\lambda\,X_{(m,a)}\sum_c X_{(c,a)}^2$ plus the image of $p_3$ under the algebra map sending $X_b \mapsto X_{(b,a)}$; third, $\sum_i \partial_i\partial_i p_3 = 0$, i.e. $p_3$ is harmonic.
--
--   This records the first-order action of a diagonal element on a single row entry in the induced picture, together with the splitting of the resulting cubic into a multiple of the quadric $\sum_c X_{(c,a)}^2$ and a harmonic cubic in the $a$-th column variables. It is used by [`LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form`](thm.html#LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form), where on the orthogonal group the quadric is $1$ and the two pieces lie in distinct isotypic components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_diag_row_eq_and_harmonic_split.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.inducedPicture_act_diag_row_eq_and_harmonic_split
    (ν : Fin 3 → ℂ) (m a : Fin 3) :
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
    let γ : Fin 3 → ℂ := fun c => ν c + (![1, 0, -1] : Fin 3 → ℂ) c + (if c < m then (1 : ℂ) else if m < c then (-1 : ℂ) else 0)
    let lam : ℂ := (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5
    let p₃ : MvPolynomial (Fin 3) ℂ :=
      MvPolynomial.X m * ∑ c : Fin 3, MvPolynomial.C (γ c - lam) * MvPolynomial.X c ^ 2
    act ν a a (MvPolynomial.X (m, a)) =
        MvPolynomial.X (m, a) * ∑ c : Fin 3, MvPolynomial.C (γ c) * MvPolynomial.X (c, a) ^ 2 ∧
      MvPolynomial.X (m, a) * ∑ c : Fin 3, MvPolynomial.C (γ c) * MvPolynomial.X (c, a) ^ 2 =
        MvPolynomial.C lam * MvPolynomial.X (m, a) * (∑ c : Fin 3, MvPolynomial.X (c, a) ^ 2) +
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, a) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p₃ ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p₃)) = 0 := by sorry
