-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
-- name    : ModularCurve.qExpansion_E4_eq_map_eisenstein4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/24fcb766-5d41-5d56-976b-59ad4bde647b
-- title:
--   q-expansion of E₄ equals 1+240sumσ₃(n)qⁿ
-- statement:
--   The statement compares two power series with no hypotheses or parameters. On the analytic side, `UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄` is Mathlib's $q$-expansion, with respect to the period $1$, of the function underlying the weight-$4$ normalised Eisenstein series `ModularForm.E₄` on the upper half-plane; it is the element of $\mathbb{C}[[q]]$ whose $n$-th coefficient is the $n$-th Taylor coefficient at $q=0$ of the function of $q=e^{2\pi i\tau}$ induced by $E_4$. On the formal side, [`ModularCurve.eisenstein4`](def/ModularCurve_X0.html#L111) is the power series over $\mathbb{Z}$ whose $n$-th coefficient is $1$ when $n=0$ and $240\sum_{d\mid n} d^3$ otherwise, the sum being over the divisors of $n$ in the sense of `Nat.divisors`; `PowerSeries.map (Int.castRingHom ℂ)` applies the canonical ring homomorphism $\mathbb{Z}\to\mathbb{C}$ to each coefficient. The assertion is that these two elements of $\mathbb{C}[[q]]$ coincide, i.e. that $E_4(\tau) = 1 + 240\sum_{n\ge 1}\sigma_3(n)q^n$ coefficientwise as formal power series.
--
--   This is the classical $q$-expansion of the normalised weight-$4$ Eisenstein series for $\mathrm{SL}_2(\mathbb{Z})$. It identifies the purely formal integral series used in the $q$-expansion description of modular curves and their function fields with the analytic modular form `ModularForm.E₄`, and is used by the level-structure and Tate-curve computations that invoke $E_4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpansion_E4_eq_map_eisenstein4 : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := by sorry
