-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_theorem_6_1
-- name    : OblivEllipsoid.Infeas.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:38.194072+00:00
-- url     : https://prove2.me/theorems/94c74ac7-e174-41d9-a1b5-c956a3b6a4b6
-- title:
--   Theorem 6.1 — exact update form with factor above (m²−1)/m²
-- statement:
--   Suppose $d>0$, $(\ell,\Lambda)$ is certified, $f(d,\ell)=1$, and constraint $j$ has violation strictly between zero and its slab radius. If the intermediate scale $f(d,\ell^{(1)})$ is positive, then the Procedure 3 output satisfies
--   $$d^{(3)}=\alpha(d,\ell)\left(d+\frac{2}{m-1}\frac{1}{\gamma_j(d,\ell)^2}e_j\right),\qquad\alpha(d,\ell)>\frac{m^2-1}{m^2}.$$
--
--   This gives the weight update form used by the potential decrease result.
--
--   **Formalization Note** Assumption 1.1 is explicit. The functions $\ell^{(1)}$ and $d^{(3)}$ are exactly the updates in (18) and (21)–(24), shared with the procedure relation.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 19, Theorem 6.1

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Theorem 6.1, p. 19. -/
theorem theorem_6_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < col A j ⬝ᵥ y A u d ell - u j)
    (hle : col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ∃ alpha : ℝ, (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) < alpha ∧
      d3 A u d ell j = alpha •
        (d + ((2 / ((m : ℝ) - 1)) *
          (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1) := by sorry

end OblivEllipsoid.Infeas
