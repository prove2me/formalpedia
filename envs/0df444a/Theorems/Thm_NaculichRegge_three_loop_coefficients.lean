-- Prove2me | Theorems.Thm_NaculichRegge_three_loop_coefficients
-- name    : NaculichRegge.three_loop_coefficients
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:04:46.426247+00:00
-- url     : https://prove2.me/theorems/7a469fa2-810f-4ec8-942d-1010e4411757
-- title:
--   Three-loop Regge coefficients $B^{(3)}_{ik}$ in terms of colour-ordered amplitudes (eq. (4.22))
-- statement:
--   If $\mathcal A^{(3)}=A_1^{(0)}\tilde a^3\big[B_{00}N^3C_{00}+B_{11}N^2C_{11}+B_{21}NC_{21}+B_{22}NC_{22}+B_{31}C_{31}+B_{32}C_{32}+B_{33}C_{33}\big]$ has colour-ordered amplitudes $A_\lambda=A^{(3)}_\lambda$ and $\kappa=A_1^{(0)}\tilde a^3$, then
--   $$\begin{aligned}\kappa B_{00}&=\tfrac12(A_1-A_3)+\tfrac5{144}(A_4-A_6)-\tfrac1{144}(A_7-A_9),\\ \kappa B_{11}&=-\tfrac{13}{12}(A_1+A_3)+\tfrac1{48}(A_4+A_6)+\tfrac1{48}(A_7+A_9),\\ \kappa B_{21}&=\tfrac34(A_1+A_3)-\tfrac3{16}(A_4+A_6)+\tfrac5{16}(A_7+A_9)+\tfrac14A_8,\\ \kappa B_{22}&=-\tfrac5{36}(A_4-A_6)+\tfrac1{36}(A_7-A_9),\\ \kappa B_{31}&=-\tfrac14(A_1+A_3)+\tfrac1{16}(A_4+A_6)-\tfrac3{16}(A_7+A_9)-\tfrac14A_8,\\ \kappa B_{32}&=-\tfrac1{12}(A_4-A_6)-\tfrac1{12}(A_7-A_9),\\ \kappa B_{33}&=\tfrac13(A_1+A_3)-\tfrac1{12}(A_4+A_6)-\tfrac1{12}(A_7+A_9).\end{aligned}$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 15, eqs. (4.21)–(4.22)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eq. (4.22): the three-loop Regge-basis coefficients in terms of the
colour-ordered amplitudes `A_λ^{(3)}`. -/
theorem three_loop_coefficients (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    κ * B (0, 0) = 1/2 * (colorOrderedAmp 3 κ B 1 - colorOrderedAmp 3 κ B 3)
        + 5/144 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        - 1/144 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (1, 1) = -13/12 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        + 1/48 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        + 1/48 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9) ∧
    κ * B (2, 1) = 3/4 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        - 3/16 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        + 5/16 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9)
        + 1/4 * colorOrderedAmp 3 κ B 8 ∧
    κ * B (2, 2) = -5/36 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        + 1/36 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (3, 1) = -1/4 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        + 1/16 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        - 3/16 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9)
        - 1/4 * colorOrderedAmp 3 κ B 8 ∧
    κ * B (3, 2) = -1/12 * (colorOrderedAmp 3 κ B 4 - colorOrderedAmp 3 κ B 6)
        - 1/12 * (colorOrderedAmp 3 κ B 7 - colorOrderedAmp 3 κ B 9) ∧
    κ * B (3, 3) = 1/3 * (colorOrderedAmp 3 κ B 1 + colorOrderedAmp 3 κ B 3)
        - 1/12 * (colorOrderedAmp 3 κ B 4 + colorOrderedAmp 3 κ B 6)
        - 1/12 * (colorOrderedAmp 3 κ B 7 + colorOrderedAmp 3 κ B 9) := by sorry

end NaculichRegge
