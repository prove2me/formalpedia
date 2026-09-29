-- Prove2me | Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
-- name    : ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/d02e9984-6c25-5365-9ad8-253c78498df5
-- title:
--   Partial Atkin–Lehner involution inverts Ogg's unit
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$. Work inside the field $\mathbb{Q}((\mathfrak q))$ of rational Laurent series, and for $M\ge 1$ let [`ModularCurve.modularFunctionFieldFull M`](def/ModularCurve_X0.html#L305) be the intermediate field obtained by adjoining to $\mathbb{Q}$ the set of series $j(\mathfrak q^d)$ for the nonzero divisors $d$ of $M$. Let $\Delta(\mathfrak q)$ denote [`ModularCurve.deltaSeries`](def/ModularCurve_ModularUnit.html#L107), namely $\mathfrak q\prod_{n\ge1}(1-\mathfrak q^n)^{24}$ written as a Laurent series, and let $u=$ [`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127) be $\Delta(\mathfrak q)\cdot\Delta(\mathfrak q^{p})^{-1}$, the inverse taken in $\mathbb{Q}((\mathfrak q))$. Assume given a proof `hmem` that $u$ lies in [`ModularCurve.modularFunctionFieldFull (N * p)`](def/ModularCurve_X0.html#L305). Let $\sigma=$ [`ModularCurve.atkinLehnerInvolutionFull N p`](def/ModularCurve_AtkinLehnerPartial.html#L21) be the $\mathbb{Q}$-algebra automorphism of that field defined as a choice of automorphism exchanging $j(\mathfrak q^{d})$ and $j(\mathfrak q^{dp})$ for every nonzero divisor $d$ of $N$, when such an automorphism exists, and the identity otherwise. The assertion is that the Laurent series underlying $\sigma(\langle u,\mathtt{hmem}\rangle)$ equals $p^{12}\cdot u^{-1}$, the scalar $p^{12}\in\mathbb{Q}$ acting on $\mathbb{Q}((\mathfrak q))$.
--
--   This is the transformation law of Ogg's modular unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^{p})$ on $X_0(Np)$ under the partial Atkin–Lehner involution $w_p$, in the $\mathfrak q$-expansion presentation of the function field at the cusp $\infty$. It feeds the construction of units and of explicit models and quotients of modular curves at level $Np$ used later in the formalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p)) :
    ((ModularCurve.atkinLehnerInvolutionFull N p ⟨ModularCurve.modularUnitSeries p, hmem⟩ :
        ModularCurve.modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) =
      (p : ℚ) ^ 12 • (ModularCurve.modularUnitSeries p)⁻¹ := by sorry
