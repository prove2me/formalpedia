-- Prove2me | Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three
-- name    : ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/b9a76b73-9e40-5abf-9162-e6b375e5bbf2
-- title:
--   Odd-weight integral form with ℚ(ζ₃)-rational twist, 3 ∣ d
-- statement:
--   Let $M$ be a non-zero natural number with $M \le 2$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $3 \mid \gamma_{1,1}$ (the lower right entry, in Lean's $0$-based indexing). Then there are an integer $k'$, a modular form $h$ of weight $k'$ for the subgroup $\Gamma_1(3M)$ of $\mathrm{GL}_2(\mathbb{R})$, and a power series $r$ with integer coefficients, such that: $k'$ is odd; the image of $r$ under $\mathbb{Z} \to \mathbb{C}$ coincides with the width-one $q$-expansion of $h$ (this is the predicate [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), so $h$ has integral Fourier coefficients at $\infty$); $h$ is not the zero function on the upper half-plane; and for every $n$ the $n$-th coefficient of the width-one $q$-expansion of the function $\tau \mapsto (h \mid[k'] \gamma)(3\tau)$ lies in the subfield $\mathbb{Q}(e^{2\pi i/3})$ of $\mathbb{C}$. Here the dilation $\tau \mapsto 3\tau$ is given by the action of [`ModularForm.heckeDiagMatrix 3`](def/ModularForm_HeckeOperator.html#L21), the element of $\mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix} 3 & 0 \\ 0 & 1\end{pmatrix}$.
--
--   This provides the auxiliary odd-weight form needed at the prime $3$ in the analysis of $X_1(3)$ and $X_1(6)$, where the Fourier coefficients of the twisted form must stay inside $\mathbb{Q}(\zeta_3)$; the weight-one Eisenstein series attached to the character $\chi_{-3}$, equivalently the theta series of the hexagonal lattice, and its weight-one Fricke transformation law are what make the conclusion available. It is the special case $3 \mid \gamma_{1,1}$ of [`ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two`](thm.html#ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two), which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three
    (M : ℕ) [NeZero M] (hM : M ≤ 2)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγ3 : (3 : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * 3) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix 3 • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((3 : ℕ) : ℂ))} : Set ℂ) := by sorry
