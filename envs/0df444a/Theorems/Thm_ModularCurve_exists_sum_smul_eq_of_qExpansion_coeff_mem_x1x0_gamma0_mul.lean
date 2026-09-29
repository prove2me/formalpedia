-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
-- name    : ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/87b03010-3edd-5be8-9271-80004e3e9a78
-- title:
--   Forms on Γ₁(Mp)∩Γ₀(Mpℓ) spanned over K₀ by integral forms
-- statement:
--   Fix primes $p$ and $\ell$ (supplied as `Fact` instances), a natural number $M$ assumed nonzero, a weight $k \in \mathbb{Z}$, and an intermediate field $K_0$ of the extension $\mathbb{C}/\mathbb{Q}$. Let $F$ be a modular form of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained from the congruence subgroup $\Gamma_1(Mp) \cap \Gamma_0(Mp\ell)$ of $\mathrm{SL}_2(\mathbb{Z})$, and assume that every coefficient of the $q$-expansion of $F$ of width $1$ at the cusp $\infty$ lies in $K_0$. The conclusion asserts the existence of an $n \in \mathbb{N}$, scalars $c_i \in \mathbb{C}$ for $i \in \mathrm{Fin}\,n$, modular forms $G_i$ of the same weight $k$ for the same group, and integral power series $r_i \in \mathbb{Z}[[q]]$, such that each $c_i$ lies in $K_0$, each pair $(G_i, r_i)$ satisfies [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), i.e. the coefficientwise image of $r_i$ under $\mathbb{Z} \to \mathbb{C}$ is exactly the width-$1$ $q$-expansion of $G_i$, and $F = \sum_i c_i G_i$ as functions on the upper half-plane.
--
--   This is the rationality, or $q$-expansion, principle in the form used later: a modular form whose $q$-expansion has coefficients in a subfield $K_0$ of $\mathbb{C}$ is a $K_0$-linear combination of forms with coefficients in $\mathbb{Z}$, here at the level $\Gamma_1(Mp) \cap \Gamma_0(Mp\ell)$, which is of the form $\Gamma_H(Mp\ell)$. It is used in the study of the function field of the relevant modular curve, in particular in [`ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq`](thm.html#ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq), and its proof combines the corresponding spanning statement for $\Gamma_H$-levels with a linear-algebra descent of coefficients to $K_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups in

theorem ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] {k : ℤ} (K₀ : IntermediateField ℚ ℂ)
    (F : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ K₀) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by sorry
