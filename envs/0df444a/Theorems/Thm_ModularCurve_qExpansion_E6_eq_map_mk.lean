-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
-- name    : ModularCurve.qExpansion_E6_eq_map_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/927fc600-c5bf-52bb-9838-92e6faf0f968
-- title:
--   Integral q-expansion of E₆
-- statement:
--   The assertion is an identity of formal power series over $\mathbb{C}$. On the left is `UpperHalfPlane.qExpansion 1` applied to the underlying function of `ModularForm.E₆`, i.e. the $q$-expansion of width $1$ (so $q = e^{2\pi i \tau}$) of the normalised weight-$6$ Eisenstein series for the full modular group $\mathrm{SL}_2(\mathbb{Z})$, whose $n$-th coefficient is the $n$-th Taylor coefficient at $0$ of the function on the punctured disc induced by $E_6$. On the right is the image, under the coefficient-wise map induced by the ring homomorphism $\mathbb{Z} \to \mathbb{C}$, of the power series in $\mathbb{Z}[[q]]$ whose $n$-th coefficient is $1$ for $n = 0$ and $-504 \sum_{d \mid n} d^5$ for $n \ge 1$, the sum being over the divisors of $n$. Thus $E_6$ has constant term $1$ and all coefficients integral, namely $E_6 = 1 - 504\sum_{n \ge 1}\sigma_5(n)q^n$; there are no hypotheses or variables.
--
--   This is the classical integral $q$-expansion of the weight-$6$ normalised Eisenstein series. Together with the analogous expansions for $E_4$ and $\Delta$ it supplies integral series with constant term $1$ by which forms of low weight may be multiplied into weight $12$; it is invoked in the construction of weight-one Tate-curve base changes and cusp data on modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane ModularForm Finset

theorem ModularCurve.qExpansion_E6_eq_map_mk :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by sorry
