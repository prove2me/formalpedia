-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_2
-- name    : OblivEllipsoid.Infeas.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:31.47004+00:00
-- url     : https://prove2.me/theorems/c57f56fe-ee90-495d-94b4-6d22c875761d
-- title:
--   Proposition 5.2 — a narrow most-violated slab yields a certificate
-- statement:
--   Under the setup of Proposition 5.1, choose an index $i$ maximizing $a_h^\top y(d,\ell)-u_h$ over all constraints. If $\gamma_i(d,\ell)<\tau(A,u)$, then
--   $$\bar\lambda_i=\tilde\lambda_i+e_i$$
--   is a type-L certificate: $A\bar\lambda_i=0$, $\bar\lambda_i\ge0$, and $u^\top\bar\lambda_i<0$.
--
--   This links the condition measure to the certificate update and the stopping test of OEA.
--
--   **Formalization Note** The maximizer is a hypothesis on the selected index, preserving all argmax ties. Assumption 1.1 is explicit.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 15, Proposition 5.2

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Proposition 5.2, p. 15. -/
theorem proposition_5_2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m)
    (hmax : ∀ h : Fin m, col A h ⬝ᵥ y A u d ell - u h ≤
      col A i ⬝ᵥ y A u d ell - u i)
    (hsmall : slabRadius A u d ell i < tau A u) :
    IsAlt A u (lamTilde A u d ell Lam i + Pi.single i 1) := by sorry

end OblivEllipsoid.Infeas
