-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_3
-- name    : OblivEllipsoid.Infeas.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:29.072229+00:00
-- url     : https://prove2.me/theorems/04218158-ed7b-47e9-aba5-088622e5c7e3
-- title:
--   Proposition 5.3 — Procedure 2 returns a type-L certificate
-- statement:
--   Give Procedure 2 positive weights $d$, certified lower bounds $(\ell,\Lambda)$, $f(d,\ell)\le0$, and a center violating at least one constraint. The procedure has an admissible output, and every possible output $\bar\lambda$ satisfies
--   $$A\bar\lambda=0,\qquad\bar\lambda\ge0,\qquad u^\top\bar\lambda<0.$$
--
--   Existence records the well-definedness asserted before the procedure; universal validity covers its unconstrained selections of indices and positive step sizes.
--
--   **Formalization Note** Assumption 1.1 is explicit. Procedure 2's relation encodes the ordered test $\ell\nleq u$ and all subsequent choices.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, pp. 16–17, Procedure 2 and Proposition 5.3

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Proposition 5.3, p. 17, including the procedure's well-definedness. -/
theorem proposition_5_3 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell ≤ 0)
    (hcenter : ¬ IsFeasible A u (y A u d ell)) :
    (∃ out, Proc2 A u d ell Lam out) ∧
      (∀ out, Proc2 A u d ell Lam out → IsAlt A u out) := by sorry

end OblivEllipsoid.Infeas
