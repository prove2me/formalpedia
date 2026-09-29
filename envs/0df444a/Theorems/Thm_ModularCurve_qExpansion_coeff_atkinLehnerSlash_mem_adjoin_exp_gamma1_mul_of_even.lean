-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
-- name    : ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b2e1dba4-df4e-5393-88f5-f1727a2c0e27
-- title:
--   Coefficients of (f|_kγ)(pτ) lie in ℚ(ζₚ), k even
-- statement:
--   Let $p$ be a prime and $M \ge 1$ an integer with $p \nmid M$, let $k$ be an even integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(Mp)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume $f$ has an integral $q$-expansion at infinity in the sense of the predicate [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37): there is a power series $p_0$ over $\mathbb{Z}$ whose image under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ is the width-one $q$-expansion of $f$, i.e. the expansion in $q = e^{2\pi i \tau}$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{1,1}$, the lower right entry $d$ of $\gamma$, and let $n$ be a natural number. Write $F(\tau) = (f \mid_k \gamma)(\mathrm{heckeDiagMatrix}(p) \cdot \tau)$, where [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) is the upper triangular matrix $\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$, so that its Möbius action sends $\tau$ to $p\tau$. Then the $n$-th coefficient of the width-one $q$-expansion of $F$ lies in the subfield $\mathbb{Q}\bigl(e^{2\pi i/p}\bigr)$ of $\mathbb{C}$ generated over $\mathbb{Q}$ by $e^{2\pi i/p}$.
--
--   This is the even-weight half of the assertion that the Fourier coefficients of the Atkin–Lehner transform $f\mid W_p$ of an integral form on $\Gamma_1(Mp)$ generate a subfield of the $p$-th cyclotomic field $\mathbb{Q}(\zeta_p)$. It is combined with its odd-weight counterpart to give the statement for arbitrary weight, which in turn feeds the rationality input to level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
