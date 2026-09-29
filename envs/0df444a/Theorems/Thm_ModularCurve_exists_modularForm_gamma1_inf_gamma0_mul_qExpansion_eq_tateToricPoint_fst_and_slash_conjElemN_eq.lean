-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
-- name    : ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/02853f1d-c8ea-5000-9341-38432c8f872e
-- title:
--   Weight-two toric division values on Γ₁(n)∩Γ₀(Nn)
-- statement:
--   Let $N$ and $n$ be non-zero natural numbers. The assertion is the existence of a family $X \colon \mathbb{C}^{\times} \to$ (modular forms of weight $2$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by $\Gamma_1(n) \cap \Gamma_0(Nn) \le \mathrm{SL}_2(\mathbb{Z})$), subject to two conditions. First, for every $c \in \mathbb{C}^{\times}$ with $c^n = 1$ and $c \neq 1$, the $q$-expansion of $X_c$ at $\infty$ with period $1$, regarded as a Laurent (Hahn) series over $\mathbb{Z}$, equals $\tfrac{1}{12}$ plus the first component of [`ModularCurve.tateToricPoint`](def/ModularCurve_KatzLevelPCusps.html#L20) $\mathbb{C}\,N\,c$, that is, plus the power series whose constant coefficient is $c(1-c)^{-2}$ and whose $m$-th coefficient for $m \ge 1$ is $\sum_{d \mid m,\ N \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[\,N \mid m\,]\sum_{e \mid m/N} e$. Second, for every $\rho \in \Gamma_0(n) \le \mathrm{SL}_2(\mathbb{Z})$ and every $c$ with $c^n = 1$, $c \neq 1$, the weight-$2$ slash of the function underlying $X_c$ by [`ModularCurve.FullLevel.conjElemN`](def/ModularCurve_FullLevelLevelAutAt.html#L13) $N\,\rho$, the real matrix $\begin{pmatrix} a & b/N \\ Nc' & d\end{pmatrix}$ attached to $\rho = \begin{pmatrix} a & b \\ c' & d\end{pmatrix}$, is the function underlying $X_{c^{d}}$, the exponent being the integer lower-right entry $d$ of $\rho$. No condition is imposed on $X_c$ for $c$ not an $n$-th root of unity or for $c = 1$.
--
--   Classically these are the weight-two Weierstrass division values $(2\pi i)^{-2}\wp(s/n; \mathbb{Z} + \mathbb{Z}N\tau)$ attached to the toric point $u = c$ of the Tate curve with parameter $q^N$, together with their permutation law $X_c \mapsto X_{c^d}$ under $\Gamma_0(n)$ conjugated by $\mathrm{diag}(N,1)$. The statement supplies the analytic input, in the shape of a family of genuine modular forms matching the prescribed Tate-curve Laurent expansions, for the comparison of Katz-style forms with classical ones at the cusps carried out in [`ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
    (N n : ℕ) [NeZero N] [NeZero n] :
    ∃ X : ℂˣ → ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(X c))) =
          (ModularCurve.tateToricPoint ℂ N c).1 + HahnSeries.C ((12 : ℂ)⁻¹)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 n → ∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        (⇑(X c) ∣[(2 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(X (c ^ ((ρ 1 1 : ℤ))))) := by sorry
