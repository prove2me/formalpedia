-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1
-- name    : ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/ee3cd7f0-26e3-5847-8a61-62e54c6db374
-- title:
--   Forms on Γ₁(N) are spanned by integral q-expansions
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k$ be an integer, and let $F$ be a modular form of weight $k$ for the subgroup $\Gamma_1(N)$ of $\mathrm{GL}(2,\mathbb{R})$ (the congruence subgroup regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$). The assertion is that there exist a natural number $n$, complex scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$, modular forms $G_i$ of the same weight $k$ for the same group, and formal power series $r_i \in \mathbb{Z}[[q]]$, such that two conditions hold. First, for each $i$ the form $G_i$ has integral $q$-expansion witnessed by $r_i$, in the precise sense that the image of $r_i$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ is equal to the $q$-expansion of width $1$ of the function $G_i$ on the upper half-plane. Second, as functions on the upper half-plane, $F$ equals $\sum_{i} c_i \cdot G_i$ (the equality being of the coerced functions $\mathbb{H} \to \mathbb{C}$, pointwise scalar multiplication, rather than an identity in the module of modular forms).
--
--   This is the statement that $M_k(\Gamma_1(N))$ is spanned over $\mathbb{C}$ by forms with integral Fourier coefficients at $\infty$, i.e. the complex-analytic shadow of the integrality (or $q$-expansion principle) statement $M_k(\Gamma_1(N)) = M_k(\Gamma_1(N),\mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{C}$. It feeds the construction of integral bases and rationality statements for spaces of forms, being used for the corresponding spanning results over $\Gamma_H$, for a variant formulated via $q$-expansion coefficients, and for a dimension bound on families of forms with integral expansions that are linearly independent over $\mathbb{C}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1
    (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by sorry
