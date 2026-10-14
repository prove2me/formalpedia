-- Prove2me | Theorems.Thm_IntMul_HvdH_rho_bounds
-- name    : IntMul.HvdH.rho_bounds
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:47:18.182036+00:00
-- url     : https://prove2.me/theorems/7f2b6d89-09e1-4b96-85e3-05066b9291ed
-- title:
--   Fixed-point rounding: $|\rho(u)|\le|u|$ and $|\rho(u)-u|<\sqrt2\cdot2^{-p}$
-- statement:
--   Let $p\ge0$ and let $\rho(u)=2^{-p}\rho_0(2^pu)$ be rounding towards zero to precision $p$, as defined in `IntMul_HvdH_FixedPoint`. Then for every $u\in\mathbb C$,
--   $$|\rho(u)|\le|u|\qquad\text{and}\qquad|\rho(u)-u|<\sqrt2\cdot2^{-p}.$$
--   In particular $\rho$ maps the closed unit disc into the fixed-point unit disc $\tilde{\mathbb C}_\circ$. These are the basic properties of $\rho$ stated in §2.2 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.2, p. 9 (properties of rho)

import Definitions.Def_IntMul_HvdH_FixedPoint

namespace IntMul.HvdH
theorem rho_bounds (p : ℕ) (u : ℂ) :
    ‖rho p u‖ ≤ ‖u‖ ∧ ‖rho p u - u‖ < Real.sqrt 2 * ((2 : ℝ) ^ p)⁻¹ := by sorry
end IntMul.HvdH
