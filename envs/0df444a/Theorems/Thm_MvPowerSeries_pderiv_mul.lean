-- Prove2me | Theorems.Thm_MvPowerSeries_pderiv_mul
-- name    : MvPowerSeries.pderiv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/ef2329d7-3282-596e-9a21-a12d83f8ca07
-- title:
--   Leibniz rule for `pderivLin` on multivariate power series
-- statement:
--   Let $\sigma$ be an index type and $R$ a commutative ring, let $i \in \sigma$, and let $f, g \in R[[X_s : s \in \sigma]]$ be multivariate formal power series. Here [`MvPowerSeries.pderivLin i`](def/FormalGroup_NSeries.html#L122) denotes the $R$-linear operator on `MvPowerSeries σ R` defined coefficientwise by the rule that the coefficient of a monomial exponent $d : \sigma \to_0 \mathbb{N}$ in `pderivLin i F` is $(d(i)+1)$ times the coefficient of $d + e_i$ in $F$, where $e_i =$ `Finsupp.single i 1`; $R$-linearity of this assignment is part of the definition. The theorem asserts the product rule for this operator: $$\mathrm{pderivLin}_i(f \cdot g) = \mathrm{pderivLin}_i(f)\cdot g + f \cdot \mathrm{pderivLin}_i(g),$$ an identity of multivariate power series over $R$. Equivalently, `pderivLin i` is a derivation of the ring `MvPowerSeries σ R` (here only the Leibniz identity itself is asserted, not packaged as a `Derivation`).
--
--   This is the Leibniz rule for formal partial differentiation of multivariate power series, in the coefficientwise form in which the operator is set up in this development. It is used in [`MvPowerSeries.pderiv_subst`](thm.html#MvPowerSeries.pderiv_subst) (differentiation of a substitution) and, through it, in the identity [`WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed`](thm.html#WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed) concerning the formal group law attached to a Weierstrass curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_pderiv_mul.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem MvPowerSeries.pderiv_mul
    {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPowerSeries σ R) :
    MvPowerSeries.pderivLin i (f * g) = MvPowerSeries.pderivLin i f * g + f * MvPowerSeries.pderivLin i g := by sorry
