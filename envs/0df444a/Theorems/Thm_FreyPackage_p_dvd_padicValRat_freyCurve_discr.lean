-- Prove2me | Theorems.Thm_FreyPackage_p_dvd_padicValRat_freyCurve_discr
-- name    : FreyPackage.p_dvd_padicValRat_freyCurve_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a0341ac6-10f9-534b-bb34-4dcaa66f85e8
-- title:
--   p divides v_ℓ(Δ) for the Frey curve over ℚ
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p\ge 5$ satisfying $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0 \pmod 2$, and let `P.freyCurve` be the associated Weierstrass curve over $\mathbb{Q}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $\ell$ be a prime number with $\ell\neq 2$. The assertion is that the integer $p$, viewed in $\mathbb{Z}$, divides $\mathrm{padicValRat}\,\ell\,(\Delta)$, the $\ell$-adic valuation (an element of $\mathbb{Z}$) of the discriminant $\Delta$ of `P.freyCurve` computed from the above coefficients by the usual Weierstrass formula. Thus the valuation of the discriminant of the $\mathbb{Q}$-model at every odd prime, in particular at $\ell=p$, is a multiple of $p$.
--
--   This is the divisibility condition on discriminant valuations underlying Serre's notion of a representation being "peu ramifiée" at an odd prime, stated here for the rational Weierstrass model of the Frey curve rather than for its integral model; it is used by [`FreyCurve.isPeuRamifieeAt_odd_of_integralForm`](thm.html#FreyCurve.isPeuRamifieeAt_odd_of_integralForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_p_dvd_padicValRat_freyCurve_discr.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.p_dvd_padicValRat_freyCurve_discr (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (P.p : ℤ) ∣ padicValRat ℓ P.freyCurve.Δ := by sorry
