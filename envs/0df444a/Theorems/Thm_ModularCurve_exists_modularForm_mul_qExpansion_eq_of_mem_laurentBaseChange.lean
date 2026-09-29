-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
-- name    : ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/e4d12051-6158-51d7-955c-a9f4ee27bc79
-- title:
--   Elements of ℂF_N are ratios of forms on Γ₀(N)
-- statement:
--   Let $N$ be a positive integer and let $x$ be a Laurent series over $\mathbb{C}$ in the variable $q$. Assume $x$ lies in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103), that is, in the intermediate field of $\mathbb{C}((q))$ obtained by adjoining to $\mathbb{C}$ the image, under the coefficientwise ring homomorphism [`ModularCurve.coeffEmb ℂ`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to \mathbb{C}$, of the subfield [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305) of $\mathbb{Q}((q))$, the latter being generated over $\mathbb{Q}$ by the set [`ModularCurve.divisorExpansions N`](def/ModularCurve_X0.html#L297) of series $\mathrm{qExpand}_{\mathbb{Q}}\, d\ \mathrm{jq}$ for the nonzero divisors $d \mid N$ (the expansions of $j$ in $q^d$). The conclusion asserts the existence of an integer $k$ and of two modular forms $g, h$ of weight $k$ for the congruence subgroup $\Gamma_0(N)$ with $h \neq 0$, such that in $\mathbb{C}((q))$ one has $x \cdot \tilde h = \tilde g$, where $\tilde g, \tilde h \in \mathbb{C}[[q]] \subseteq \mathbb{C}((q))$ denote the $q$-expansions of $g$ and $h$ at $i\infty$ taken with width $1$. Thus $x$ is the $q$-expansion of the ratio $g/h$ of two forms of equal weight on $\Gamma_0(N)$.
--
--   This is one half of the classical identification of the function field $\mathbb{C}(X_0(N)) = \mathbb{C}(j(q^d) : d \mid N)$ with the field of weight-$0$ meromorphic modular functions for $\Gamma_0(N)$, in the concrete shape needed to evaluate elements of the Laurent-series field at points of the upper half-plane. It is used throughout the dictionary between the algebraic model of $X_0(N)$ and the analytic picture, for instance in the treatment of Abel–Jacobi maps, period lattices and Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in

theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange (N : ℕ)
    [NeZero N] (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
