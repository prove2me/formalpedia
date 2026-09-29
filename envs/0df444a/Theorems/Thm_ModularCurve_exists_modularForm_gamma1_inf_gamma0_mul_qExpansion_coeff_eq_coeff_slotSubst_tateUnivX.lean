-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
-- name    : ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/6c82978c-604a-5b85-9953-2374b54e0a3a
-- title:
--   Non-toric division values as weight-two forms on Γ₁(n)∩Γ₀(Nn)
-- statement:
--   Let $N$ and $n$ be nonzero natural numbers with $N \mid n$, let $c$ be a unit of $\mathbb{C}$ with $c^{n} = 1$, and let $b$ be a natural number with $0 < b < N$. The assertion is the existence of a modular form $F$ of weight $2$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained from the subgroup $\Gamma_1(n) \cap \Gamma_0(Nn)$ of $\mathrm{SL}_2(\mathbb{Z})$, such that for every natural number $m$ the $m$-th coefficient of the $q$-expansion of $F$ taken with period $1$ equals $\tfrac1{12}$ when $m = 0$ and $0$ otherwise, plus the $m$-th coefficient of the one-variable complex power series obtained from the two-variable integral series [`ModularCurve.tateUnivX`](def/ModularCurve_TateSlots.html#L10) by substituting $c\,X^{b}$ for the first variable and $c^{-1}X^{N-b}$ for the second. Here [`ModularCurve.tateUnivX`](def/ModularCurve_TateSlots.html#L10) has, at the exponent vector $e$, coefficient $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, coefficient $e_0 - e_1$ when $e_1 < e_0$ and $e_0 - e_1$ divides $e_1$, coefficient $e_1 - e_0$ when $e_0 < e_1$ and $e_1 - e_0$ divides $e_1$, and $0$ in the remaining cases.
--
--   In classical terms this produces, as a weight-two form on $\Gamma_1(n) \cap \Gamma_0(Nn)$, the normalised Weierstrass division value at the non-toric torsion point $c\,q^{b}$ of the Tate curve $\mathrm{Tate}(q^{N})$, its $q$-expansion being $\tfrac1{12}$ plus the abscissa series; for $n = N$ these are the forms $f_2^{\bar v}$ of Diamond–Shurman read in the variable $N\tau$. It is used in the full-level Diamond arguments on variable changes for the weight-one Tate base and the associated cusp and toric-point data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
    (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (c : ℂˣ) (hc : c ^ n = 1) (b : ℕ) (hb0 : 0 < b) (hbN : b < N) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff m =
        (if m = 0 then (1 / 12 : ℂ) else 0) +
          PowerSeries.coeff m (ModularCurve.slotSubst ℂ N c b ModularCurve.tateUnivX) := by sorry
