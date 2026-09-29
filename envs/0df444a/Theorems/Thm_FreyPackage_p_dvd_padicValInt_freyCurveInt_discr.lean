-- Prove2me | Theorems.Thm_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr
-- name    : FreyPackage.p_dvd_padicValInt_freyCurveInt_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/fad8cea1-e017-5d4a-8cb8-e0138b844ca3
-- title:
--   p divides v_ℓ(Δ) of the Frey curve at odd ℓ
-- statement:
--   Let $P$ be a Frey package, that is: nonzero integers $a$, $b$, $c$, a prime $p$ with $5 \le p$, the relation $a^p + b^p = c^p$, $\gcd(a,b) = 1$, the congruence $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Attached to $P$ is the integral Weierstrass curve `P.freyCurveInt` over $\mathbb{Z}$ with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -(a^p)(b^p)/16$, $a_6 = 0$, the divisions being integer divisions, and $\Delta$ denotes its Weierstrass discriminant in the sense of Mathlib. Let $\ell$ be a prime with $\ell \ne 2$. The conclusion is a divisibility of natural numbers: $p$ divides $\operatorname{padicValInt} \ell\, \Delta$, the $\ell$-adic valuation of the integer $\Delta$. No assumption relating $\ell$ to $p$ is made, so the case $\ell = p$ is included.
--
--   For a semistable elliptic curve the condition $p \mid v_\ell(\Delta_{\min})$ at an odd prime $\ell$ is exactly the condition that the mod-$p$ representation be finite (peu ramifiée) at $\ell$; this is the arithmetic input, at $\ell = p$ in particular, for the level-lowering step applied to the Frey curve. The statement is used in the corresponding assertion for the rational model, [`FreyPackage.p_dvd_padicValRat_freyCurve_discr`](thm.html#FreyPackage.p_dvd_padicValRat_freyCurve_discr).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.p_dvd_padicValInt_freyCurveInt_discr (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : P.p ∣ padicValInt ℓ P.freyCurveInt.Δ := by sorry
