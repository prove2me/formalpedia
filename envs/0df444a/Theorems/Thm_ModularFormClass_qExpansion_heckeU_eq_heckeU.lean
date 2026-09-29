-- Prove2me | Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
-- name    : ModularFormClass.qExpansion_heckeU_eq_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d5bd031c-2d8b-50e7-a6f7-abc2bfb1d9a1
-- title:
--   q-expansion of Uₚf equals formal Uₚ of the q-expansion
-- statement:
--   Let $F$ be a type whose elements act as functions from the upper half-plane to $\mathbb{C}$, let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ and $k$ an integer, and assume $F$ is a type of modular forms of weight $k$ for $\Gamma$ in the sense of Mathlib's `ModularFormClass`. Let $f : F$, and assume $1$ is a strict period of $\Gamma$, i.e. $1 \in \Gamma.\mathrm{strictPeriods}$, so that $f$ admits a $q$-expansion of width $1$. Let $p$ be a natural number with $p \neq 0$. The operator $\mathrm{heckeU}\,k\,p$ sends a function $g$ on the upper half-plane to $\sum_{j<p} g \mid[k] \begin{pmatrix}1&j\\0&p\end{pmatrix}$, the weight-$k$ slash action summed over the $p$ upper-triangular matrices $\mathrm{heckeMatrix}\,p\,j$; the formal operator $\mathrm{PowerSeries.heckeU}\,p$ sends a power series $g$ to the series whose $n$-th coefficient is the $(pn)$-th coefficient of $g$. The assertion is the equality of formal power series over $\mathbb{C}$: the width-$1$ $q$-expansion of $\mathrm{heckeU}\,k\,p\,f$ equals $\mathrm{PowerSeries.heckeU}\,p$ applied to the width-$1$ $q$-expansion of $f$; in classical terms, if $f=\sum_n a_nq^n$ then $U_pf=\sum_n a_{pn}q^n$.
--
--   This is the standard description of the Hecke operator $U_p$ on $q$-expansions (as in Diamond–Shurman, Prop. 5.2.2). It is the power-series packaging of the corresponding coefficientwise identity, and serves as the bridge between the analytic operator defined by slash actions on functions and the formal operator on power series used in the eigenform and lattice arguments downstream, such as the integrality and mod-$p$ eigenvalue statements for cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.qExpansion_heckeU_eq_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeU k p ⇑f)
      = PowerSeries.heckeU p (UpperHalfPlane.qExpansion 1 ⇑f) := by sorry
