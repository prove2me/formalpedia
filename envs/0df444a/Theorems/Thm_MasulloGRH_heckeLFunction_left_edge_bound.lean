-- Prove2me | Theorems.Thm_MasulloGRH_heckeLFunction_left_edge_bound
-- name    : MasulloGRH.heckeLFunction_left_edge_bound
-- status  : Proved
-- author  : @flashonfire
-- created : 2026-11-21T19:13:33.738677+00:00
-- url     : https://prove2.me/theorems/97e23589-b051-4707-a47b-b61edb243ed0
-- title:
--   Bound $L_f(-\delta+it,\chi)\ll|t|^{n(1/2+\delta)}$ on the left edge
-- statement:
--   Let $F$ be a number field of degree $n=[F:\mathbb Q]$, $\chi$ a Hecke character of $F$ and $\delta>0$. Then on the vertical line $\operatorname{Re}s=-\delta$,
--   $$|L_f(-\delta+it,\chi)|\le C\,|t|^{\,n\left(\frac12+\delta\right)}\qquad\text{for all } |t|\ge T,$$
--   for suitable constants $C$ and $T$.
--
--   This is the left-edge input for the convexity argument. By the functional equation of the completed $L$-function (Proposition 3.2.1.3, `MasulloGRH.completedHeckeLFunction_properties`), $L_f(-\delta+it,\chi)$ equals an entire nowhere-vanishing factor $\varepsilon(s)$, times the gamma ratio $\gamma_{\chi^{-1}}(1+\delta-it)/\gamma_\chi(-\delta+it)$, times $L_f(1+\delta-it,\chi^{-1})$. Here $\varepsilon(s)$ is of the form $W\cdot A^{1/2-s}$ with $|W|=1$. The last factor is bounded (right-edge bound for $\chi^{-1}$). By Stirling's formula, each real place contributes $\asymp|t|^{1/2+\delta}$ to the gamma ratio and each complex place $\asymp|t|^{1+2\delta}$. The archimedean twists of $\chi$ only shift $t$ by a bounded amount. The total is $\asymp|t|^{n(1/2+\delta)}$. The intended Stirling input is the proved `Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im` (two-sided bounds for $\Gamma$ on vertical strips).
--
--   **Role.** Reconstruction: a supporting lemma for the Phragmén–Lindelöf proof of the Convexity Bound, Proposition B.1.1.3.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix B, Proposition B.1.1.3 (Convexity Bound), p. 591. Reconstruction: supporting lemma for the standard Phragmén–Lindelöf proof of B.1.1.3.

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

namespace MasulloGRH

theorem heckeLFunction_left_edge_bound
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| →
      ‖heckeLFunction χ (((-δ : ℝ) : ℂ) + t * Complex.I)‖ ≤
        C * |t| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 + δ)) := by
  sorry

end MasulloGRH
