-- Prove2me | Theorems.Thm_IntMul_HvdH_rho0C_sub_half
-- name    : IntMul.HvdH.rho0C_sub_half
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:47:19.475372+00:00
-- url     : https://prove2.me/theorems/3d0de766-d7a5-4238-aa3c-c90a7c8f8eaf
-- title:
--   Rounding a half-integer Gaussian point moves it by at most $1/\sqrt2$ (Lemma 2.1)
-- statement:
--   Let $u\in\mathbb C$ be such that $2\,\mathrm{Re}\,u$ and $2\,\mathrm{Im}\,u$ are integers. Then rounding towards zero componentwise moves $u$ by at most $1/\sqrt2$:
--   $$|\rho_0(u)-u|\le\frac{\sqrt2}{2}.$$
--   This is the estimate in the proof of Lemma 2.1 (addition/subtraction) of Harvey–van der Hoeven. For fixed-point inputs $u,v\in2^{-p}\mathbb Z[i]$, $w=\tfrac12(u\pm v)$ satisfies the hypothesis after scaling by $2^p$, so $\tilde w=\rho(w)$ has error $\varepsilon(\tilde w)=2^p|\tilde w-w|<1$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.2, proof of Lemma 2.1

import Definitions.Def_IntMul_HvdH_FixedPoint

namespace IntMul.HvdH
theorem rho0C_sub_half (u : ℂ) (hre : ∃ n : ℤ, 2 * u.re = n) (him : ∃ n : ℤ, 2 * u.im = n) :
    ‖rho0C u - u‖ ≤ Real.sqrt 2 / 2 := by sorry
end IntMul.HvdH
