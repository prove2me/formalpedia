-- Prove2me | Theorems.Thm_IntMul_HvdH_fp_mul_error
-- name    : IntMul.HvdH.fp_mul_error
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:32:03.951992+00:00
-- url     : https://prove2.me/theorems/a342895f-1015-4c83-af79-9100f93dee32
-- title:
--   Fixed-point product error (Lemma 2.4 / Corollary 2.10)
-- statement:
--   Let $p\ge0$, let $u,v\in\mathbb C$ and approximations $\tilde u,\tilde v$ with $|u|\le1$ and $|\tilde v|\le1$, and suppose $2^p|\tilde u-u|\le\varepsilon_u$ and $2^p|\tilde v-v|\le\varepsilon_v$. Then the rounded product $\tilde w=\rho(\tilde u\tilde v)$ (rounding towards zero to precision $p$, see `IntMul_HvdH_FixedPoint`) satisfies
--   $$2^p\,|\tilde w-uv|<\varepsilon_u+\varepsilon_v+2.$$
--   This is Corollary 2.10 of Harvey–van der Hoeven (combining Lemma 2.4 and Lemma 2.9).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.6 (Lemma 2.4, Corollary 2.10)

import Definitions.Def_IntMul_HvdH_FixedPoint

namespace IntMul.HvdH
theorem fp_mul_error (p : ℕ) (u v ut vt : ℂ) (hu : ‖u‖ ≤ 1) (hvt : ‖vt‖ ≤ 1)
    (eu ev : ℝ) (hut : (2 : ℝ) ^ p * ‖ut - u‖ ≤ eu) (hvt' : (2 : ℝ) ^ p * ‖vt - v‖ ≤ ev) :
    (2 : ℝ) ^ p * ‖rho p (ut * vt) - u * v‖ < eu + ev + 2 := by sorry
end IntMul.HvdH
