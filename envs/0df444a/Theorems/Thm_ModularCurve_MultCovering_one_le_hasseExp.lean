-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
-- name    : ModularCurve.MultCovering.one_le_hasseExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/2650903e-1871-5ed9-bc62-10807230d310
-- title:
--   Hasse members of the good family have positive exponent
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ belongs to the non-units of $A$, with residue field $k = \mathrm{ResidueField}\,A$ assumed of characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`: a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi_p \equiv (X^p - Y)(X - Y^p) \bmod p$, integrality of the two Hecke operators $\bar\alpha$, $\bar\beta$ at level $1$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ of $A$ together with a level-one prolongation pair $R$ for it, a set $S_1$ of places of the level-$p$ modular function field over $\overline{\mathbb{Q}}$, a finite set of places of the level-one modular function field over $k$ consisting exactly of the supersingular places, and finiteness of the supersingular $j$-set with cardinality $m = p/12 + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$, subject to the supply conditions `ChartFstSupply` for $R$ and $S_1$. Let $r$ be a natural number and $\Phi$ a good family context `FamCtx p r`: family data $(t_l)_{l<r}$ forming an embedding basis of the Riemann–Roch space of the embedding divisor at level $1\cdot p$, with $t_0 = 1$, whose reductions in the infinity chart and in the zero chart have the prescribed shapes $\mathrm{ss}(\bar\jmath)\,P_l(\bar\jmath)$ with degree and spanning conditions relative to $m$. Then for every index $l$ with $l \ge 1$ one has $1 \le \mathrm{hasseExp}(\Phi, l)$, the natural number obtained as `Nat.toNat` of the Hasse content `hasseContent` of the family at $l$.
--
--   This records that the Hasse members of a good family, those with index $l \ge 1$, have strictly positive exponent at the $0$-cusp, so that the corresponding renormalised functions $p^{-n_l} t_l$ are genuinely rescaled; it is the lower bound complementing the upper bounds on these exponents, and it feeds the comparison of the two Gauss lattices attached to the charts $V_\infty$ and $V_0 = w_p V_\infty$ of $X_0(p)$. It is used by the cross-comparison estimates on the annuli of the multiplicative covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_one_le_hasseExp.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.one_le_hasseExp (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := by sorry
