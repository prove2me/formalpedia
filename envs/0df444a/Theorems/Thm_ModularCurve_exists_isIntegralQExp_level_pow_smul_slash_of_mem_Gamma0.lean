-- Prove2me | Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
-- name    : ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/73920bd3-395f-50d4-9d00-938c4b20e83d
-- title:
--   Integral q-expansions up to Mᵃ under Γ₀(M)-translation
-- statement:
--   Let $M$ be a positive natural number and $k$ an integer. Let $f$ be a modular form of weight $k$ for the image of $\Gamma_1(M)$ in $\mathrm{GL}(2,\mathbb{R})$, and let $p \in \mathbb{Z}[[X]]$ be a power series with the property expressed by [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), namely that the power series obtained from $p$ by applying the ring homomorphism $\mathbb{Z} \to \mathbb{C}$ coefficientwise is the $q$-expansion of $f$ of period $1$ (so $f$ has integral Fourier coefficients at $\infty$ in the parameter $q = e^{2\pi i \tau}$, with $p$ recording them). Let $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lie in $\Gamma_0(M)$. The conclusion asserts the existence of a natural number $a$, a modular form $f_1$ of weight $k$ for $\Gamma_1(M)$, and a power series $p_1 \in \mathbb{Z}[[X]]$ such that the complex image of $p_1$ is the $q$-expansion of $f_1$ of period $1$, and such that, as functions on the upper half-plane, $f_1 = M^a \cdot (f \mid_k \gamma)$, the scalar $M^a$ acting on the weight-$k$ slash translate of $f$ by $\gamma$.
--
--   This is the assertion that the action of $\Gamma_0(M)$ (through the diamond operators) on forms of weight $k$ on $\Gamma_1(M)$ with integral expansion at $\infty$ introduces denominators dividing a power of the level only, a sharpening of [`ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0`](thm.html#ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0), where merely some nonzero integer clears the denominators. It is used in the treatment of diamond operators modulo $\ell$ for primes $\ell$ not dividing $M$, for instance by the uniqueness and compatibility statements for [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (a : ℕ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ a) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by sorry
