-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
-- name    : ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e8442930-5ee5-59ff-93d9-696191b4c325
-- title:
--   Odd weight: ℚ(ζₚ)-rationality of f∣_kγ at pτ
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \nmid M$, let $k$ be an odd integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(Mp)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume $f$ has an integral $q$-expansion in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37): there is a power series $p_0$ over $\mathbb{Z}$ whose image under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of $f$ of width $1$ (that is, in $q = e^{2\pi i \tau}$). Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{1,1}$, the lower right entry of $\gamma$. Then for every natural number $n$, the $n$-th coefficient of the width-$1$ $q$-expansion of the function $\tau \mapsto (f \mid_k \gamma)(\mathrm{heckeDiagMatrix}(p) \cdot \tau)$, where [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ acting on the upper half plane by $\tau \mapsto p\tau$, belongs to the intermediate field $\mathbb{Q}\big(e^{2\pi i / p}\big)$ of $\mathbb{C}$ generated over $\mathbb{Q}$ by the single element $e^{2\pi i / p}$.
--
--   This is the odd weight half of the classical rationality statement that the Fourier coefficients of the Atkin–Lehner transform $f \mid W_p$ of an integral form on $\Gamma_1(Mp)$ lie in the cyclotomic field $\mathbb{Q}(\zeta_p)$, the transform being realised here as $\tau \mapsto (f\mid_k\gamma)(p\tau)$ for $\gamma \in \Gamma_0(M)$ with $p$ dividing its lower right entry. It is combined with the even weight case in [`ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul`](thm.html#ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul), which splits on the parity of $k$; the proof cites the even weight statement, the existence of a non-zero odd weight integral form on $\Gamma_1(Mp)$ whose transform has $\mathbb{Q}(\zeta_p)$-rational coefficients, and the fact that the transform is again a modular form of weight $k$ on $\Gamma_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
