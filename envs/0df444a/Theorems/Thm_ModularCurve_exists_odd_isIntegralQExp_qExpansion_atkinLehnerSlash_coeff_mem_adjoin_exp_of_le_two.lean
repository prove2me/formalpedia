-- Prove2me | Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two
-- name    : ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/e4ddaf0e-f0ac-5289-a6f9-6dfcd29fd55b
-- title:
--   Odd-weight integral form with ℚ(ζₚ)-rational transform, M ≤ 2
-- statement:
--   Let $p$ be a prime and $M \ge 1$ an integer with $p \nmid M$, $M \le 2$ and $Mp \ge 3$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{1,1}$ (the lower right entry, in zero-based indexing). Then there are an integer $k'$, a modular form $h$ of weight $k'$ for the image of $\Gamma_1(Mp)$ in $\mathrm{GL}_2(\mathbb{R})$, and a power series $r$ with integer coefficients, such that: $k'$ is odd; the image of $r$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of $h$ with respect to the period $1$, i.e. [`ModularCurve.IsIntegralQExp h r`](def/ModularCurve_X1.html#L37); $h$ is not the zero function on the upper half-plane; and for every $n$ the $n$-th coefficient of the period-$1$ $q$-expansion of the function $\tau \mapsto (h \mid_{k'} \gamma)(\mathrm{heckeDiagMatrix}(p) \cdot \tau)$, where $\mathrm{heckeDiagMatrix}(p)$ is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ acting on the upper half-plane (so $\tau \mapsto p\tau$), lies in the subfield $\mathbb{Q}(e^{2\pi i/p})$ of $\mathbb{C}$ generated over $\mathbb{Q}$ by $\exp(2\pi i/p)$.
--
--   This provides the auxiliary odd-weight form with integral $q$-expansion whose Atkin–Lehner type transform at $p$ has Fourier coefficients in $\mathbb{Q}(\zeta_p)$, in the residual range $M \le 2$, where $\Gamma_1(M)$ contains $-1$ and carries no odd-weight forms, so the level at $p$ must be used. It is the small-level case of [`ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp`](thm.html#ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp), which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : M ≤ 2) (hMp : 3 ≤ M * p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
