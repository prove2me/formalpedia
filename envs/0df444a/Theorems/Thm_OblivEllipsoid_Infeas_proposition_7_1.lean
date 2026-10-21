-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_proposition_7_1
-- name    : OblivEllipsoid.Infeas.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:30.879286+00:00
-- url     : https://prove2.me/theorems/87148ed9-8729-430f-8a9a-8cedf774ab84
-- title:
--   Proposition 7.1 — a bound on each slab radius
-- statement:
--   For positive weights $d$ and an ellipsoid of positive scale $f(d,\ell)>0$, each slab radius obeys
--   $$\gamma_i(d,\ell)\le\left(\frac{d_i}{f(d,\ell)}\right)^{-1/2}\qquad(i\in[m]).$$
--
--   The estimate turns growth of a normalized weight into a bound on the corresponding slab width.
--
--   **Formalization Note** Assumption 1.1, adopted throughout the paper, is explicit; the positive hypotheses keep the real power on its intended domain.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 21, Proposition 7.1

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Proposition 7.1, p. 21. -/
theorem proposition_7_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) :
    ∀ i : Fin m, slabRadius A u d ell i ≤
      (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) := by sorry

end OblivEllipsoid.Infeas
