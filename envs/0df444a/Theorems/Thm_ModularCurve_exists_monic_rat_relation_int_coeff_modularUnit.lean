-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit
-- name    : ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/516660d3-a0f3-560c-aac5-e6baab756ba2
-- title:
--   Monic relation over ℚ[j] for the modular unit Δ(q)/Δ(qᵖ)
-- statement:
--   Let $p$ be a prime. Write $u :=$ [`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127) for the rational Laurent series $\Delta\cdot(\Delta_p)^{-1}$, where $\Delta$ is [`ModularCurve.deltaSeries`](def/ModularCurve_ModularUnit.html#L107) $= q\cdot\eta$-unit series $q\prod(1-q^n)^{24}$ (the Hahn series $\mathrm{single}(1,1)$ times the power series `dedekindEtaUnitQ`) and $\Delta_p$ is its $q\mapsto q^p$ substitution `qExpand ℚ p`; and write $j :=$ [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) for the Laurent series $\mathrm{single}(-1,1)$ times the image in $\mathbb{Q}$ of the integral power series `jNum` $= E_4^3\cdot(\eta\text{-unit})^{-1}$, i.e. the $q$-expansion of the modular invariant. The assertion is that there exist a natural number $n$ and a family $S : \mathrm{Fin}\,n \to \mathbb{Q}[X]$ of polynomials such that, in the field of rational Laurent series, $$u^{n} + \sum_{i<n} S_i(j)\, u^{i} = 0,$$ where $S_i(j)$ denotes the evaluation `Polynomial.aeval` of $S_i$ at $j$, and such that moreover every coefficient of each Laurent series $S_i(j)$, at every index $k \in \mathbb{Z}$, lies in the image of $\mathbb{Z} \to \mathbb{Q}$. Thus $u$ is integral over $\mathbb{Q}[j]$ by a monic relation whose coefficient series have integer $q$-expansions; neither the value $n = p+1$ nor integrality of the polynomials $S_i$ themselves is asserted here.
--
--   This is the integrality over $\mathbb{Q}[j]$ of the modular unit $\Delta(q)/\Delta(q^p)$ on $X_0(p)$, in the $q$-expansion formulation. It is the rational-coefficient stage of the construction of the modular equation: the companion statement [`ModularCurve.exists_monic_int_relation_modularUnit`](thm.html#ModularCurve.exists_monic_int_relation_modularUnit) upgrades it to a monic relation with coefficients in $\mathbb{Z}[j]$ by an elementary descent on $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℚ),
      ModularCurve.modularUnitSeries p ^ n + ∑ i : Fin n,
        Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) *
          ModularCurve.modularUnitSeries p ^ (i : ℕ) = 0
      ∧ ∀ (i : Fin n) (k : ℤ), ∃ m : ℤ,
        (Polynomial.aeval (ModularCurve.jqModC ℚ) (S i)).coeff k = (m : ℚ) := by sorry
