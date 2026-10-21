-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_remark_1_1
-- name    : OblivEllipsoid.Infeas.remark_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:24.194067+00:00
-- url     : https://prove2.me/theorems/a2f590bf-7966-4f95-8bd6-6516ae0ed41f
-- title:
--   Remark 1.1 — a certified lower bound above the upper bound yields a certificate
-- statement:
--   Suppose $\ell_j$ is a certified lower bound on constraint $j$ with certificate $\lambda_j$, and $\ell_j>u_j$. Then the primal system is infeasible, and
--   $$\bar\lambda_j=\lambda_j+e_j$$
--   satisfies $A\bar\lambda_j=0$, $\bar\lambda_j\ge0$, and $u^\top\bar\lambda_j<0$.
--
--   This supplies the certificate returned by the immediate lower-bound test in the algorithm.
--
--   **Formalization Note** Assumption 1.1 is carried explicitly because the paper adopts it throughout, although this implication alone does not need it.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 5, Remark 1.1

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Remark 1.1, p. 5. -/
theorem remark_1_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (hA : Assumption11 A) (j : Fin m) (lj : ℝ) (lamj : Fin m → ℝ)
    (hcert : CertLBi A u j lj lamj) (hgap : u j < lj) :
    (¬ ∃ x : Fin n → ℝ, IsFeasible A u x) ∧
      IsAlt A u (lamj + Pi.single j 1) := by sorry

end OblivEllipsoid.Infeas
