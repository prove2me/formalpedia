-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily
-- name    : ModularCurve.MultCovering.mem_of_eq_sum_smul_goodFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6a7e7ac8-e1ed-5736-9b03-757941e00af7
-- title:
--   Coefficients of an ∞̄-integral combination of a good family
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$, in the sense that the image of $p$ lies in the nonunits of $A$; assume the residue field of $A$ has decidable equality and characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$: a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi \equiv (X^{p}-Y)(X-Y^{p})$ modulo $p$, integrality of the Hecke $\alpha$- and $\beta$-maps at level $1$ and prime $p$, a place specialisation $P$ together with a level-one prolongation pair $R$, a set $S_1$ of places of the base-changed modular function field of level $1\cdot p$, a finite set $W_n$ of places of the level-one function field over the residue field of $A$ consisting exactly of the supersingular places, the finiteness of the supersingular $j$-set together with the assertion that it has $\mathrm{mAnnuli}\ p$ elements, and a chart supply datum for $R$ and $S_1$. Let $r$ be a natural number and $\Psi$ a good-family context for $p$ and $r$: a family $t_0,\dots,t_{r-1}$ in the base-changed modular function field of level $1\cdot p$ which is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the embedding divisor, with $t_0 = 1$, and whose members are integral with prescribed reductions (products of the supersingular polynomial with linearly independent polynomials in $\bar j$ spanning polynomials of degree less than $\mathrm{mAnnuli}\ p$) at the infinity chart of any such chart context, and analogously at the zero chart. Let $c : \mathrm{Fin}\ r \to \overline{\mathbb Q}$ and let $x$ be an element of the base-changed modular function field of level $1\cdot p$ lying in the valuation subring of integers of the chart $\mathrm{infChart}\ \Gamma$ obtained from $\Gamma.R$, $\Gamma.S_1$ and $\Gamma.W_n$, and suppose $x = \sum_j c_j\, t_j$. Then $c_j \in A$ for every $j$.
--
--   This is the integrality half of the statement that a good family is an $A$-basis of the Gauss lattice cut out by the $\overline\infty$-chart: an $\overline{\mathbb Q}$-linear combination of the family that is integral for the chart already has all its coefficients in $A$. The argument uses the transcendence of the $q$-expansion of $j$ over the base ring, [`ModularCurve.transcendental_jqModC`](thm.html#ModularCurve.transcendental_jqModC), and the result feeds into [`ModularCurve.MultCovering.compConst_eq_compConst`](thm.html#ModularCurve.MultCovering.compConst_eq_compConst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_of_eq_sum_smul_goodFamily (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Ψ : FamCtx p r) (c : Fin r → AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * p)))
    (hx : x ∈ (infChart Γ).integers) (heq : x = ∑ j, c j • Ψ.t j) :
    ∀ j, c j ∈ A := by sorry
