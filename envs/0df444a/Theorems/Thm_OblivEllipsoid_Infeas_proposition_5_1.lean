-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_1
-- name    : OblivEllipsoid.Infeas.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:32.568772+00:00
-- url     : https://prove2.me/theorems/db8f2fb6-3283-4446-bcea-4447c33da158
-- title:
--   Proposition 5.1 — the Burrell–Todd vector certifies the slab lower bound
-- statement:
--   Let $d>0$, let $(\ell,\Lambda)$ be certified lower bounds, and suppose $f(d,\ell)=1$. For a constraint $i$, set $L_i=a_i^\top y(d,\ell)-\gamma_i(d,\ell)$, $\hat\lambda_i=\gamma_iDt-DA^\top B^{-1}a_i$, and $\tilde\lambda_i=\Lambda\hat\lambda_i^-+\hat\lambda_i^+$. Then
--   $$A\tilde\lambda_i=-a_i,\qquad\tilde\lambda_i\ge0,\qquad -u^\top\tilde\lambda_i\ge L_i.$$
--
--   The vector is a reusable certificate for the improved lower bound formed from an ellipsoid slab.
--
--   **Formalization Note** The paper's standing Assumption 1.1 is explicit. The hypothesis $f=1$ supplies both the positive-volume condition and the stated normalization.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 15, Proposition 5.1 and eq. (17)

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Proposition 5.1, p. 15. -/
theorem proposition_5_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m) :
    CertLBi A u i (Lb A u d ell i) (lamTilde A u d ell Lam i) := by sorry

end OblivEllipsoid.Infeas
