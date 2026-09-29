-- Prove2me | Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp
-- name    : ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/cf0a9571-26d2-5c1b-bcbc-600e321a1343
-- title:
--   Existence of an odd-weight integral form with ℚ(ζₚ)-coefficients
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \nmid M$ and $Mp \ge 3$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{1,1}$, the lower-right entry of $\gamma$ in Lean's zero-based indexing. Then there exist an integer $k'$, a modular form $h$ of weight $k'$ for the image of $\Gamma_1(Mp)$ in $\mathrm{GL}_2(\mathbb{R})$, and a power series $r$ with integer coefficients, such that: $k'$ is odd; $r$ is an integral $q$-expansion for $h$ in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), i.e. the image of $r$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the width-one $q$-expansion of $h$; the underlying function $\mathbb{H} \to \mathbb{C}$ of $h$ is not identically zero; and for every $n \in \mathbb{N}$ the $n$-th coefficient of the width-one $q$-expansion of the function $\tau \mapsto (h \mid_{k'} \gamma)(\mathrm{heckeDiagMatrix}(p) \cdot \tau)$ lies in the intermediate field $\mathbb{Q}(e^{2\pi i/p})$ of $\mathbb{C}$. Here $\mathrm{heckeDiagMatrix}(p)$ is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$, so that the function in question is $\tau \mapsto (h \mid_{k'} \gamma)(p\tau)$.
--
--   This supplies the auxiliary odd-weight form used to reduce the odd-weight case of the statement that the Fourier coefficients of the Atkin–Lehner transform of an integral form lie in $\mathbb{Q}(\zeta_p)$ to the even-weight case, by multiplying the given form by $h$ and dividing the resulting $q$-series. It is cited by [`ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd`](thm.html#ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hMp : 3 ≤ M * p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
