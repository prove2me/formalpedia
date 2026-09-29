-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0
-- name    : ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/415ca679-9956-5b76-ae8f-f89a63d106f3
-- title:
--   Forms with K₀-rational q-expansions on Γ₁(M)∩Γ₀(p)
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \nmid M$, let $k$ be an integer, and let $K_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{C}$. Write $\Gamma$ for the subgroup of $\mathrm{GL}(2,\mathbb{R})$ determined by $\Gamma_1(M) \cap \Gamma_0(p) \leq \mathrm{SL}(2,\mathbb{Z})$, and let $F$ be a modular form of weight $k$ for $\Gamma$ all of whose $q$-expansion coefficients at the cusp $\infty$, taken with width $1$, lie in $K_0$. Then there are a natural number $n$, scalars $c_i \in \mathbb{C}$ for $i \in \{0,\dots,n-1\}$, modular forms $G_i$ of the same weight $k$ for the same group $\Gamma$, and integral power series $r_i \in \mathbb{Z}[[q]]$, such that each $c_i$ lies in $K_0$; each $G_i$ has integral $q$-expansion witnessed by $r_i$, meaning that the image of $r_i$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the width-$1$ $q$-expansion of $G_i$; and $F = \sum_i c_i G_i$ as functions on the upper half-plane.
--
--   This is the rationality (or $q$-expansion principle) statement that $M_k(\Gamma_1(M)\cap\Gamma_0(p))$ has a spanning set of forms with $q$-expansions in $\mathbb{Z}[[q]]$, so that a form whose coefficients lie in a subfield $K_0$ of $\mathbb{C}$ is already a $K_0$-linear combination of such integral forms. It is used to descend Atkin–Lehner computations at $p$ to the field $K_0$, as in [`ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0`](thm.html#ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups in

theorem ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (K₀ : IntermediateField ℚ ℂ)
    (F : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ K₀) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by sorry
