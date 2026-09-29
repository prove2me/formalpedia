-- Prove2me | Theorems.Thm_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
-- name    : ModularCurve.mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/bb4db783-881f-54d7-b19d-698978fedabe
-- title:
--   Rationality of q-expansions of ratios of forms on Γ₀(N)
-- statement:
--   Let $N$ be a positive natural number, $k$ an integer, and let $g,h$ be modular forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$, with $h \neq 0$. Let $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism from the algebraic closure of $\mathbb{Q}$ (as constructed by `AlgebraicClosure`) to $\mathbb{C}$, and let $x$ be a formal Laurent series with coefficients in $\overline{\mathbb{Q}}$. Assume that the series obtained from $x$ by applying $\sigma$ to each coefficient, [`ModularCurve.coeffMap σ x`](def/ModularCurve_LaurentCoeff.html#L16), equals the quotient, formed in $\mathbb{C}((q))$, of the $q$-expansion of $g$ of width $1$ by the $q$-expansion of $h$ of width $1$, each power series being regarded as a Laurent series. The conclusion is that $x$ belongs to [`ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103), that is, to the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images under $\overline{\mathbb{Q}} \supseteq \mathbb{Q}$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the Laurent series [`ModularCurve.qExpand ℚ d jq`](def/ModularCurve_X0.html#L25) for the positive divisors $d$ of $N$.
--
--   This is the $q$-expansion principle in the form identifying those Laurent series with algebraic coefficients whose complex specialisation is the expansion of a ratio of equal-weight forms on $\Gamma_0(N)$ with elements of the modular function field $\overline{\mathbb{Q}}(j(q^d) : d \mid N)$. It is used by [`ModularCurve.exists_coeffMap_diffQExpBar_eq_qExpansion`](thm.html#ModularCurve.exists_coeffMap_diffQExpBar_eq_qExpansion) in establishing rationality properties of $q$-expansions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div (N : ℕ) [NeZero N]
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (σ : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : ModularCurve.coeffMap σ x =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    x ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldFull N) := by sorry
