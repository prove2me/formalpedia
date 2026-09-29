-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint
-- name    : ModularCurve.exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/afb2ba29-e4a5-53de-941c-7e4caa330db5
-- title:
--   Toric Tate abscissa as weight-two form on Γ₁(N)∩Γ₀(N²)
-- statement:
--   Let $N$ be a nonzero natural number and let $c$ be a unit of $\mathbb{C}$ with $c^N = 1$ and $c \neq 1$. The assertion is that there exists a modular form $F$ of weight $2$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained from the intersection $\Gamma_1(N) \cap \Gamma_0(N^2)$ inside $\mathrm{SL}_2(\mathbb{Z})$, such that for every natural number $n$ the $n$-th coefficient of the $q$-expansion of $F$ of width $1$ equals $\tfrac1{12}$ when $n = 0$, plus $0$ otherwise, added to the coefficient at the integer $n$ of the first component of [`ModularCurve.tateToricPoint ℂ N c`](def/ModularCurve_KatzLevelPCusps.html#L20). That first component is the Laurent series over $\mathbb{C}$ attached to the power series whose $0$-th coefficient is $c\,\bigl(\mathrm{Ring.inverse}(1-c)\bigr)^2$, i.e. $c/(1-c)^2$, and whose $m$-th coefficient for $m \geq 1$ is
--   $$\sum_{d \mid m,\ N \mid d} \frac{m}{d}\Bigl(c^{m/d} + c^{-m/d}\Bigr) \;-\; 2\Bigl[N \mid m\Bigr]\sum_{e \mid m/N} e .$$
--   Since $d \mid m$ and $N \mid d$ force $N \mid m$, these coefficients vanish unless $N \mid m$, and for $m = Nm'$ they equal $\sum_{d \mid m'} d\,(c^d + c^{-d}) - 2\sigma_1(m')$; thus the $q$-expansion of $F$ is $\tfrac1{12} + X(c, q^N)$, with $X$ the abscissa of Tate's uniformisation.
--
--   This is the toric case of the classical fact that the weight-two division values of the Weierstrass $\wp$-function, here $(2\pi i)^{-2}\wp(a/N;\ \mathbb{Z} + \mathbb{Z}N\tau)$ for $c = e^{2\pi i a/N}$, are modular forms, on $\Gamma_1(N) \cap \Gamma_0(N^2)$ after the substitution $\tau \mapsto N\tau$, and identifies their $q$-expansions with the $x$-coordinate of the toric $N$-torsion point $u = c$ on the Tate curve over $\mathbb{C}((q))$. It is used in the full-level comparison results [`ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom`](thm.html#ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom) and [`ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level`](thm.html#ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level), where cusp data on the Tate curve must be matched with classical modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint
    (N : ℕ) [NeZero N] (c : ℂˣ) (hc : c ^ N = 1) (hc1 : c ≠ 1) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N ^ 2) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff n =
        (if n = 0 then (1 / 12 : ℂ) else 0) + (ModularCurve.tateToricPoint ℂ N c).1.coeff (n : ℤ) := by sorry
