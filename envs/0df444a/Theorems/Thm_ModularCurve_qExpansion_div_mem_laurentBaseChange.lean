-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange
-- name    : ModularCurve.qExpansion_div_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8e68c997-676d-54b2-8853-62ef0dd2ea16
-- title:
--   Ratios of q-expansions of Γ₀(N)-forms lie in ℂ· F_N
-- statement:
--   Let $N$ be a natural number, assumed nonzero, let $k$ be an integer, and let $g,h$ be modular forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$, with $h \neq 0$. Write $\tilde g, \tilde h \in \mathbb{C}[[q]]$ for the $q$-expansions of the underlying functions $g, h \colon \mathbb{H} \to \mathbb{C}$ taken with period $1$, regarded via the inclusion $\mathbb{C}[[q]] \hookrightarrow \mathbb{C}((q))$ as Laurent series, and form the quotient $\tilde g/\tilde h$ in the field $\mathbb{C}((q))$ of Laurent series over $\mathbb{C}$. The assertion is that this quotient belongs to [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103), that is, to the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image, under the coefficientwise map $\mathbb{Q}((q)) \to \mathbb{C}((q))$ induced by $\mathbb{Q} \to \mathbb{C}$, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the Laurent series $\mathrm{qExpand}\,\mathbb{Q}\,d\,\mathrm{jq}$, i.e. the substitutions $q \mapsto q^{d}$ of the $q$-expansion of $j$, as $d$ runs over the nonzero divisors of $N$.
--
--   This is the bridge from the analytic theory to the formal $q$-expansion model of the function field of $X_0(N)$: every modular function of level $N$ presented as a ratio of two forms of equal weight on $\Gamma_0(N)$ is realised inside the compositum of $\mathbb{C}$ with the field $\mathbb{Q}(j(q^d) : d \mid N)$ of formal expansions, at arbitrary level rather than only prime level. It is used in the comparison of points of $X_0(N)$ with places of its function field, in the realisation of meromorphic data by modular functions, and in the study of expansions multiplied by powers of the $j$-series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.qExpansion_div_mem_laurentBaseChange (N : ℕ) [NeZero N] {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0) :
    ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) := by sorry
