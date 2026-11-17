-- Prove2me | Theorems.Thm_N25_Endgame_ternary_zeta_initial_coefficients25
-- name    : N25.Endgame.ternary_zeta_initial_coefficients25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:21.162539+00:00
-- url     : https://prove2.me/theorems/50df520a-4f3c-48d5-87e6-df5048e41ac0
-- title:
--   The zeta identity fixes the first four numerator coefficients
-- statement:
--   Let $L∈ℤ[T]$ satisfy $L(0)=1$, and let $A:ℕ→ℤ$. If $$(1-T)(1-3T)∑_{n≥0}A_nT^n=L(T),$$ then $A_0=1$ and the coefficients of $T,T^2,T^3,T^4$ are respectively $A_1-4A_0$, $A_2-4A_1+3A_0$, $A_3-4A_2+3A_1$, and $A_4-4A_3+3A_2$. This extracts the initial zeta data.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.ternary_zeta_initial_coefficients25
    (L : Polynomial ℤ) (A : ℕ → ℤ)
    (hzero : L.coeff 0 = 1)
    (h : (1 - PowerSeries.X) * (1 - PowerSeries.C (3 : ℤ) * PowerSeries.X) *
      PowerSeries.mk A = (L : PowerSeries ℤ)) :
    A 0 = 1 ∧ L.coeff 1 = A 1 - 4 * A 0 ∧
      L.coeff 2 = A 2 - 4 * A 1 + 3 * A 0 ∧
      L.coeff 3 = A 3 - 4 * A 2 + 3 * A 1 ∧
      L.coeff 4 = A 4 - 4 * A 3 + 3 * A 2 := by sorry
