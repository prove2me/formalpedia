-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- name    : ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/5636cc31-83b4-5857-9119-65b75b184405
-- title:
--   Weight-three toric family on Γ₁(n)∩Γ₀(Nn)
-- statement:
--   Let $N$ and $n$ be non-zero natural numbers. The assertion is the existence of a family $Y : \mathbb{C}^\times \to$ (modular forms of weight $3$ for the image in $\mathrm{GL}_2(\mathbb{R})$ of the subgroup $\Gamma_1(n)\cap\Gamma_0(Nn)$ of $\mathrm{SL}_2(\mathbb{Z})$) with two properties. First, for every $c \in \mathbb{C}^\times$ with $c^n = 1$ and $c \neq 1$, the $q$-expansion of $Y_c$ taken with period $1$, viewed as a Laurent series over $\mathbb{C}$, equals $2\,t_2 + t_1$, where $(t_1,t_2) =$ [`ModularCurve.tateToricPoint`](def/ModularCurve_KatzLevelPCusps.html#L20) $\mathbb{C}$ $N$ $c$ is the pair of power series whose constant terms are $c(1-c)^{-2}$ and $c^2(1-c)^{-3}$ and whose $m$-th coefficients, for $m \ge 1$, are $\sum_{d \mid m,\ N \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[N \mid m]\sigma_1(m/N)$ and $\sum_{d \mid m,\ N \mid d}\bigl(\binom{m/d}{2}c^{m/d} - \binom{m/d+1}{2}c^{-m/d}\bigr) + [N \mid m]\sigma_1(m/N)$ respectively, with $\sigma_1(k) = \sum_{e \mid k} e$. Second, for every $\rho \in \Gamma_0(n)$ and every $c$ with $c^n = 1$, $c \neq 1$, the weight-$3$ slash action of [`ModularCurve.FullLevel.conjElemN`](def/ModularCurve_FullLevelLevelAutAt.html#L13) $N$ $\rho$, that is of the determinant-one real matrix $\begin{pmatrix} \rho_{00} & \rho_{01}/N \\ N\rho_{10} & \rho_{11}\end{pmatrix}$, sends $Y_c$ to $Y_{c^{\rho_{11}}}$, the exponent being the lower-right integer entry of $\rho$. No condition is imposed on $Y_c$ for $c$ which is not a non-trivial $n$-th root of unity.
--
--   The forms $Y_c$ are the weight-three Eisenstein series of level $\Gamma(n)$ attached to the torsion index $(0,s)$ with $c = \zeta_n^{s}$, normalised so that their expansion at the cusp $\infty$ reproduces the function $2y + x = -(2\pi i)^{-3}\wp'$ evaluated at the toric point $u = c$ of the Tate curve with parameter $q^N$, together with the permutation law for the index under $\Gamma_0(n)$ conjugated by $\mathrm{diag}(N,1)$. It feeds the construction of modular forms with prescribed values at the cusps of the relevant modular curve in [`ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
    (N n : ℕ) [NeZero N] [NeZero n] :
    ∃ Y : ℂˣ → ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 3,
      (∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Y c))) =
          2 * (ModularCurve.tateToricPoint ℂ N c).2 + (ModularCurve.tateToricPoint ℂ N c).1) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 n → ∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        (⇑(Y c) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(Y (c ^ ((ρ 1 1 : ℤ))))) := by sorry
