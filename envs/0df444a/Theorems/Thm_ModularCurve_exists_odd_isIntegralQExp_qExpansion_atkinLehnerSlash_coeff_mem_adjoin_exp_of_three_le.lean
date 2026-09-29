-- Prove2me | Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le
-- name    : ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/27152ba2-d901-56b2-9ef1-40b92eedaa73
-- title:
--   Odd-weight integral form on Γ₁(Mp) with cyclotomic dilated q-coefficients
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \nmid M$ and $3 \le M$, and let $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{11}$ (the lower right entry). The assertion is that there are an integer $k'$, a modular form $h$ of weight $k'$ for the image of $\Gamma_1(Mp)$ in $\mathrm{GL}(2,\mathbb{R})$, and a formal power series $r$ over $\mathbb{Z}$, such that: $k'$ is odd; [`ModularCurve.IsIntegralQExp h r`](def/ModularCurve_X1.html#L37) holds, i.e. pushing $r$ forward along $\mathbb{Z} \to \mathbb{C}$ gives the $q$-expansion of $h$ of period $1$, so that $h$ has integral Fourier coefficients; $h$ is not the zero function on the upper half plane; and for every $n$ the $n$-th coefficient of the period-$1$ $q$-expansion of $\tau \mapsto (h \mid_{k'} \gamma)(p\tau)$ — the dilation being by [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21), the upper triangular matrix with diagonal $(p,1)$ — lies in the subfield $\mathbb{Q}(e^{2\pi i/p})$ of $\mathbb{C}$. The proof uses neither the hypothesis $p \nmid M$ nor the hypothesis $p \mid \gamma_{11}$.
--
--   This is the case $M \ge 3$ of the construction of an auxiliary odd-weight form with integral Fourier coefficients whose Atkin–Lehner type transform at $p$ has $q$-expansion coefficients in the $p$-th cyclotomic field; it feeds the general statement [`ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp`](thm.html#ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp), where the small-level cases are handled separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : 3 ≤ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
