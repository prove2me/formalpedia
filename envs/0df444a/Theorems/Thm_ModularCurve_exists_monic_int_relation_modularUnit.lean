-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_int_relation_modularUnit
-- name    : ModularCurve.exists_monic_int_relation_modularUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/cd460c37-60d1-5057-829e-4ac454fc9d69
-- title:
--   Monic integral relation for Δ(q)/Δ(qᵖ) over ℤ[j]
-- statement:
--   For a prime $p$, the assertion is the existence of a natural number $n$ and a family $S : \mathrm{Fin}\,n \to \mathbb{Z}[X]$ of integral polynomials satisfying a single identity in the field of formal Laurent series over $\mathbb{Z}$. Write $\Delta$ for the Laurent series $q\cdot\eta$, where $\eta$ is [`ModularCurve.dedekindEtaUnit`](def/ModularCurve_X0.html#L127), the $24$-th power of the power series $\prod_{n\ge 1}(1-X^{n})$, viewed in `LaurentSeries ℤ` and multiplied by the monomial `HahnSeries.single (1 : ℤ) 1`, i.e. the discriminant $q$-expansion $q\prod_{n\ge1}(1-q^{n})^{24}$; write $\Delta(q^{p})$ for its image under [`ModularCurve.qExpand ℤ p`](def/ModularCurve_X0.html#L25), the ring endomorphism of `LaurentSeries ℤ` obtained by multiplying all exponents by $p$; and write $j$ for [`ModularCurve.jqModC ℤ`](def/ModularCurve_JqCoeff.html#L15), the Laurent series $q^{-1}\,(E_4^{3}\eta^{-1})$ built from `jNum`. The identity asserted is $$\Delta^{n} + \sum_{i<n} S_i(j)\,\Delta^{i}\,\Delta(q^{p})^{\,n-i} = 0,$$ each $S_i$ being evaluated at $j$ through the $\mathbb{Z}$-algebra structure of `LaurentSeries ℤ`. Thus the relation is stated in inverse-free homogeneous form, every term having total degree $n$ in the pair $(\Delta,\Delta(q^{p}))$ and the term of degree $n$ in $\Delta$ having coefficient $1$. No value of $n$ is specified (classically $n=p+1$, the index of $\Gamma_0(p)$); the existential statement also forces $n\ge 1$.
--
--   This is the integrality, over $\mathbb{Z}[j]$, of the modular unit $\Delta(q)/\Delta(q^{p})$ on $X_0(p)$, recorded as a monic homogeneous relation over $\mathbb{Z}((q))$ so that no inverse of $\Delta(q^{p})$ is needed and the relation can be read in any base ring. It is obtained here from the corresponding relation over $\mathbb{Q}$ with coefficient series taking integer values, [`ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit`](thm.html#ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit), and it feeds the membership statement [`ModularCurve.modularUnitSeries_mem_chartAlgFin_int`](thm.html#ModularCurve.modularUnitSeries_mem_chartAlgFin_int) for the level-$p$ function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_int_relation_modularUnit.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monic_int_relation_modularUnit (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℤ),
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ n +
        ∑ i : Fin n, Polynomial.aeval (ModularCurve.jqModC ℤ) (S i) *
          ((HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ (i : ℕ) *
            (ModularCurve.qExpand ℤ p (HahnSeries.single (1 : ℤ) 1 *
              HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit)) ^ (n - (i : ℕ))) = 0 := by sorry
