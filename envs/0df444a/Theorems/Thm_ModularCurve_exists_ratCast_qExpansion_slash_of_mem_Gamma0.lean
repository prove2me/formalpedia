-- Prove2me | Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
-- name    : ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/31aaf82e-a346-51e6-8114-eafcfedadbcf
-- title:
--   Rationality of q-expansions under slashing by Γ₀(M)
-- statement:
--   Let $M$ be a positive natural number, let $k$ be an integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(M)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume that the $q$-expansion of $f$ at $\infty$ of width $1$, i.e. the expansion in $q = e^{2\pi i \tau}$ given by `UpperHalfPlane.qExpansion 1`, has all its coefficients rational: for every natural number $n$ there is $r \in \mathbb{Q}$ with $n$-th coefficient equal to the image of $r$ in $\mathbb{C}$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$, and let $n$ be a natural number. Then the $n$-th coefficient of the width-$1$ $q$-expansion of the function $\mathbb{H} \to \mathbb{C}$ obtained by applying the weight-$k$ slash operator $\cdot \mid_k \gamma$ to the underlying function of $f$ is again the image of a rational number. The conclusion concerns the slashed function as a function on the upper half-plane; no modular form structure on it is asserted.
--
--   This is the rationality half of the classical statement that the diamond operators $\langle \delta \rangle$ on forms for $\Gamma_1(M)$ are defined over $\mathbb{Q}$ with respect to the expansion at the cusp $\infty$: since $\Gamma_1(M)$ is normal in $\Gamma_0(M)$, slashing by $\gamma \in \Gamma_0(M)$ preserves the space of forms of weight $k$ on $\Gamma_1(M)$ and preserves rationality of Fourier coefficients. It feeds the results on bases of cusp forms with rational (or integral) $q$-coefficients stable under slashing and under Hecke and diamond operators, such as [`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`](thm.html#CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast) and [`CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast`](thm.html#CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n = (r : ℂ) := by sorry
