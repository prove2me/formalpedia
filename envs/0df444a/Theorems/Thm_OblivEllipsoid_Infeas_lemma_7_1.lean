-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_lemma_7_1
-- name    : OblivEllipsoid.Infeas.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:31.190502+00:00
-- url     : https://prove2.me/theorems/397dae30-a00c-44f7-b685-10238232b027
-- title:
--   Lemma 7.1 — potential function decrease
-- statement:
--   Let $(d,\ell)$ and $(\tilde d,\tilde\ell)$ have positive weights and positive scales. For a chosen $j$, suppose their normalized weights obey the update relation with $\alpha\ge(m^2-1)/m^2$. If $(d_j/f(d,\ell))^{-1/2}\ge\tau(A,u)$, then
--   $$\phi(\tilde d,\tilde\ell)\le e^{-1/(2(m+1))}\phi(d,\ell).$$
--
--   This is the per-update quantitative decrease used in the iteration bound.
--
--   **Formalization Note** The update relation is stated explicitly in Lean, with coefficient $2/(m-1)$ and $1/\gamma_j(d,\ell)^2$. Assumption 1.1 is explicit.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 22, Lemma 7.1

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Lemma 7.1, p. 22. -/
theorem lemma_7_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell dTilde ellTilde : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hdTilde : ∀ i, 0 < dTilde i)
    (hf : 0 < f A u d ell) (hfTilde : 0 < f A u dTilde ellTilde)
    (j : Fin m) (alpha : ℝ)
    (hupdate : (1 / f A u dTilde ellTilde) • dTilde = alpha •
      ((1 / f A u d ell) • d +
        ((2 / ((m : ℝ) - 1)) * (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1))
    (halpha : (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) ≤ alpha)
    (htau : tau A u ≤ (d j / f A u d ell) ^ (-(1 / 2 : ℝ))) :
    potential A u dTilde ellTilde ≤
      Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) * potential A u d ell := by sorry

end OblivEllipsoid.Infeas
