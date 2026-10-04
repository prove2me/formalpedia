-- Prove2me | Theorems.Thm_NaculichRegge_two_loop_coefficients
-- name    : NaculichRegge.two_loop_coefficients
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:04:25.794646+00:00
-- url     : https://prove2.me/theorems/c50f6af9-bbae-4ede-a8c0-00c910c4e414
-- title:
--   Two-loop Regge coefficients $B^{(2)}_{ik}$ in terms of colour-ordered amplitudes (eq. (4.18))
-- statement:
--   If $\mathcal A^{(2)}=A_1^{(0)}\tilde a^2\big[B_{00}N^2C_{00}+B_{11}NC_{11}+B_{21}C_{21}+B_{22}C_{22}\big]$ has colour-ordered amplitudes $A_\lambda=A^{(2)}_\lambda$, then
--   $$\begin{aligned}A_1^{(0)}\tilde a^2B_{00}&=\tfrac12(A_1-A_3)-\tfrac1{24}(A_7-A_9),& A_1^{(0)}\tilde a^2B_{11}&=-(A_1+A_3),\\ A_1^{(0)}\tilde a^2B_{21}&=\tfrac14(A_7+A_9),& A_1^{(0)}\tilde a^2B_{22}&=\tfrac16(A_7-A_9).\end{aligned}$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 14, eqs. (4.17)–(4.18)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eq. (4.18): the two-loop Regge-basis coefficients in terms of the colour-ordered
amplitudes `A_λ^{(2)}`. -/
theorem two_loop_coefficients (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    κ * B (0, 0) = 1/2 * (colorOrderedAmp 2 κ B 1 - colorOrderedAmp 2 κ B 3)
        - 1/24 * (colorOrderedAmp 2 κ B 7 - colorOrderedAmp 2 κ B 9) ∧
    κ * B (1, 1) = -(colorOrderedAmp 2 κ B 1 + colorOrderedAmp 2 κ B 3) ∧
    κ * B (2, 1) = 1/4 * (colorOrderedAmp 2 κ B 7 + colorOrderedAmp 2 κ B 9) ∧
    κ * B (2, 2) = 1/6 * (colorOrderedAmp 2 κ B 7 - colorOrderedAmp 2 κ B 9) := by sorry

end NaculichRegge
