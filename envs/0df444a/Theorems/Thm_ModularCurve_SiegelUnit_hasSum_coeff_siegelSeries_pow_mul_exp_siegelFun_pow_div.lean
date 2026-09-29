-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
-- name    : ModularCurve.SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e8cf29bb-9d11-5c94-80cf-fdc89369a641
-- title:
--   Formal Siegel series computes the q-expansion of gₐ^{12q}
-- statement:
--   Let $q$ be a prime, let $a\colon \mathrm{Fin}\,2 \to \mathbb{Z}/q$, write $a_0=(a\,0).\mathrm{val}$ and $a_1=(a\,1).\mathrm{val}$ for the representatives in $\{0,\dots,q-1\}$, let $\iota\colon \mathbb{Q}(\zeta_q)\to\mathbb{C}$ be a ring homomorphism from the cyclotomic field `CyclotomicField q ℚ` sending the distinguished root of unity `zetaQ q` to $e^{2\pi i/q}$, and let $\tau$ lie in the upper half-plane. Let $S_a\in\mathbb{Q}(\zeta_q)[[X]]$ be `siegelSeries q a`, the image in $\mathbb{Q}(\zeta_q)$ of the power series over $\mathbb{Z}[\zeta_q]$ given by $(1-\zeta_q^{a_1}X^{a_0})\bigl(\prod'_{n\ge 0}(1-\zeta_q^{a_1}X^{q(n+1)+a_0})\bigr)\prod'_{n\ge 0}(1-\zeta_q^{q-a_1}X^{q(n+1)-a_0})$ (the exponent $q(n+1)-a_0$ being truncated subtraction of naturals). The assertion is that the family indexed by $n\in\mathbb{N}$ with terms $\iota\bigl(\mathrm{coeff}_n(S_a^{12q})\bigr)\,e^{2\pi i n\tau/q}$ has sum $$\frac{g_{a_0,a_1}(\tau)^{12q}}{\iota\bigl(\zeta_q^{\,6a_0a_1}\bigr)\,e^{2\pi i (6a_0^2-6qa_0+q^2)\tau/q}},$$ where $g_{a_0,a_1}(\tau)=$ `siegelFun q a_0 a_1 τ` is the analytic function $-e^{\pi i a_1(a_0-q)/q^2}\,e^{\pi i((a_0/q)^2-a_0/q+1/6)\tau}\,(1-w)\prod'_{n\ge 0}(1-p^{n+1}w)(1-p^{n+1}w^{-1})$ with $p=e^{2\pi i\tau}$ and $w=e^{2\pi i(a_0\tau+a_1)/q}$.
--
--   This is the Kubert–Lang product formula for a Siegel function, in the form identifying the power-series part of the formal level-$q$ Siegel expansion, read into $\mathbb{C}$ through $\iota$ and summed at the parameter $e^{2\pi i\tau/q}$, with the analytic $q$-expansion of $g_a^{12q}$ normalised by its leading constant $\zeta_q^{6a_0a_1}$ and its fractional power of $e^{2\pi i\tau/q}$. It is the bridge between the formal function field of level $q$ and the analytic Siegel units, and is used in constructing a modular form on $\Gamma_1(q)$ whose $q$-expansion is integral with leading coefficient $1$ and all of whose slashes are integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_ModularCurve_LevelFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
    (q : ℕ) [Fact q.Prime] (a : Fin 2 → ZMod q)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum
      (fun n : ℕ => ι (PowerSeries.coeff n (siegelSeries q a ^ (12 * q))) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (q : ℂ)))
      (siegelFun q ((a 0).val : ℤ) ((a 1).val : ℤ) (τ : ℂ) ^ (12 * q) /
        (ι (zetaQ q ^ siegelConstExponent q a) *
          Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) := by sorry
