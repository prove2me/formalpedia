-- Prove2me | Theorems.Thm_IntMul_HvdH_mulZ_disc
-- name    : IntMul.HvdH.mulZ_disc
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:52:45.100261+00:00
-- url     : https://prove2.me/theorems/bfd4cfe0-4dc2-4e20-964d-897954a6fcff
-- title:
--   Fixed-point complex product stays in the unit disc
-- statement:
--   Let $p\ge0$ and let $a,b\in\mathbb Z[i]$ with $|a|,|b|\le 2^p$. The fixed-point product `mulZ p a b` $=\rho_0(ab/2^p)$, which rounds the real and imaginary parts of $ab/2^p$ towards zero, satisfies
--   $$|\,\mathrm{mulZ}_p(a,b)\,|\le 2^p .$$
--   So fixed-point multiplication at precision $p$ maps the closed unit polydisc (in units of $2^{-p}$) into itself, as in §2.3 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §2.3, Lemma 2.4

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem mulZ_disc (p : ℕ) (a b : ℤ × ℤ) (ha : ‖gC a‖ ≤ 2 ^ p) (hb : ‖gC b‖ ≤ 2 ^ p) :
    ‖gC (mulZ p a b)‖ ≤ 2 ^ p := by sorry
end IntMul.HvdH
