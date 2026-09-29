-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
-- name    : ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a29b94d8-f2d1-5cfe-998d-58a778d6133b
-- title:
--   Toric abscissa on Tate(q^N) as a weight-two form
-- statement:
--   Let $N$ and $n$ be nonzero natural numbers with $N \mid n$, and let $c$ be a unit of $\mathbb{C}$ with $c^n = 1$ and $c \neq 1$. Then there exists a modular form $F$ of weight $2$ for the subgroup of $\mathrm{GL}(2,\mathbb{R})$ determined by $\Gamma_1(n) \cap \Gamma_0(Nn) \subseteq \mathrm{SL}(2,\mathbb{Z})$ such that, for every natural number $m$, the $m$-th coefficient of the $q$-expansion of $F$ of period $1$ equals $\tfrac{1}{12}$ if $m = 0$ and $0$ otherwise, plus the coefficient in degree $m$ of the first component of $\mathrm{tateToricPoint}\ \mathbb{C}\ N\ c$. That first component is the Laurent series over $\mathbb{C}$ attached to the power series whose constant coefficient is $c\,(1-c)^{-2}$ (the inverse being taken in the sense of `Ring.inverse`) and whose $m$-th coefficient for $m \geq 1$ is $$\sum_{d \mid m,\ N \mid d} \frac{m}{d}\Bigl(c^{m/d} + c^{-m/d}\Bigr)\ -\ 2\,[\,N \mid m\,] \sum_{e \mid m/N} e .$$ Thus $F$ has $q$-expansion $\tfrac1{12}$ plus Tate's abscissa $X(c, q^N)$, the $x$-coordinate of the toric point $u = c$ on the Tate curve with parameter $q^N$.
--
--   This realises the toric division values of the Weierstrass $\wp$-function — equivalently the $x$-coordinates of toric torsion points on Tate curves — as holomorphic weight-two forms of level $\Gamma_1(n) \cap \Gamma_0(Nn)$, the divisibility $N \mid n$ serving to put the invariance group in this shape. It is used in the analysis of cusps and diamond operators for Katz forms of level structure at $p$, where the $q$-expansions of full-level forms evaluated at the Tate curve must be matched with classical modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
    (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (c : ℂˣ) (hc : c ^ n = 1) (hc1 : c ≠ 1) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff m =
        (if m = 0 then (1 / 12 : ℂ) else 0) + (ModularCurve.tateToricPoint ℂ N c).1.coeff (m : ℤ) := by sorry
