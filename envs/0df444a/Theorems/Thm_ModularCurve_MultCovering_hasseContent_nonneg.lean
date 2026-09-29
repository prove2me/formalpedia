-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseContent_nonneg
-- name    : ModularCurve.MultCovering.hasseContent_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/1de49517-60a5-5da8-ba7f-457139bdd876
-- title:
--   Non-negativity of the Hasse content of a good family
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ that lies over $p$, i.e. $p$ belongs to `A.nonunits`, together with the assumption that the residue field of $A$ has characteristic $p$ (and a decidability instance for its equality). Let $\Gamma$ be a chart context for $p$ and $A$: this packages modular polynomial data for $p$, the Kronecker congruence $\overline{\Phi}_p = (X^p - Y)(X - Y^p)$ for it, integrality of the level-one Hecke maps $\bar\alpha$ and $\bar\beta$ of index $p$, a place specialization `P` over $A$ at level $1$ with a level-one prolongation pair `R` for it, a set $S_1$ of places of the level-$1\cdot p$ modular function field over $\overline{\mathbb{Q}}$ satisfying the supply conditions `R.ChartFstSupply`, a finite set $W_n$ of places of the level-one function field over the residue field that is exactly the set of supersingular places, and the hypothesis that the supersingular $j$-set is finite of cardinality $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$. Let $r$ be a natural number and $\Phi$ a family context for $p$ and $r$: family data $(t_l)_{l < r}$ which is an embedding basis (linearly independent over $\overline{\mathbb{Q}}$ with span the Riemann–Roch space of the embedding divisor at level $1\cdot p$), with $t_0 = 1$, and whose reductions in the infinity chart and the zero chart of any chart context are prescribed as in `FamCtx` (namely $\mathrm{ss}\cdot P_l(\bar\jmath)$ with degree bounds, linear independence and spanning conditions on the polynomials $P_l$). Then for each index $l < r$ one has $0 \le \mathrm{hasseContent}\,\Phi.\mathrm{toFamData}\,l$, where this integer is, when it exists, a chosen $n \in \mathbb{Z}$ that bounds below the $p$-adic valuations of all nonzero coefficients of the Laurent series $\mathrm{zeroSeries}\,\Phi\,l$ and is attained by one of them, and is $0$ otherwise.
--
--   The quantity bounded here is the $p$-adic content of the rational $q$-expansion of the $l$-th member of the good family at the cusp $0$; the theorem says that no negative power of $p$ occurs, so the expansions at $0$ are already $p$-integral and the content requires no truncation. It is used in the analysis of the Frobenius action on the zero-chart reductions of the good family and in the construction of family data with prescribed bifiltered digits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseContent_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseContent_nonneg (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) (l : Fin r) :
    0 ≤ hasseContent Φ.toFamData l := by sorry
