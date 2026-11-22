-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_bounded_right_of_one
-- name    : MasulloGRH.heckeLFunction_bounded_right_of_one
-- status  : Proved
-- author  : @flashonfire
-- created : 2026-11-21T19:13:32.458361+00:00
-- url     : https://prove2.me/theorems/9c5ecae3-82c2-4711-8b9d-0bee09343520
-- title:
--   Boundedness of $L_f(s,\chi)$ on the line $\operatorname{Re}s=1+\delta$
-- statement:
--   Let $F$ be a number field, $\chi$ a Hecke character of $F$ and $\delta>0$. Then the finite Hecke $L$-function is bounded on the vertical line $\operatorname{Re}s=1+\delta$: there is $C$ with
--   $$|L_f(1+\delta+it,\chi)|\le C\qquad\text{for all } t\in\mathbb R.$$
--
--   On $\operatorname{Re}s>1$, $L_f(s,\chi)$ equals the absolutely convergent Euler product $\prod_v(1-\chi(\mathfrak p_v)N\mathfrak p_v^{-s})^{-1}$ (Proposition 3.2.1.3, `MasulloGRH.heckeLFunction_exists_meromorphic_continuation`). Since $|\chi(\mathfrak p_v)|\le1$, its modulus is at most $\prod_v(1-N\mathfrak p_v^{-1-\delta})^{-1}=\zeta_F(1+\delta)$, the Dedekind zeta function at a real point of absolute convergence.
--
--   **Role.** Reconstruction: the right-edge input ($\sigma=1+\delta$, exponent $0$) for the Phragmén–Lindelöf proof of the Convexity Bound, Proposition B.1.1.3.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix B, Proposition B.1.1.3 (Convexity Bound), p. 591. Reconstruction: supporting lemma for the standard Phragmén–Lindelöf proof of B.1.1.3.

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_bounded_right_of_one
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖heckeLFunction χ (((1 + δ : ℝ) : ℂ) + t * Complex.I)‖ ≤ C := by
  sorry

end MasulloGRH
