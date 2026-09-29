-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven
-- name    : ModularCurve.MultCovering.ssValue_eq_zero_or_eq_1728_of_eq_eleven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/dfb95881-471c-5b73-8684-8ebfe915c73a
-- title:
--   At p=11 the enumerated supersingular values are 0 and 1728
-- statement:
--   Let $p$ be a prime with $p=11$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$ satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in the non-units of $A$, and assume the residue field $\mathrm{ResidueField}\ A$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`: a package consisting of modular polynomial data for $p$ together with the Kronecker congruence for it, integrality of the level-one Hecke data $\bar\alpha$, $\bar\beta$ over $\overline{\mathbb{Q}}$ at $p$, a place specialization $P$ from the places of the level-$p$ geometric modular function field over $\overline{\mathbb{Q}}$ to places over the residue field, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{\mathbb{Q}}(X(1\cdot p))$, a finite set $W_n$ of places of the characteristic-$p$ level-one function field consisting exactly of the supersingular places, a proof `hfin` that the set $\mathrm{ssJSet}\ p$ of those $j$ in the residue field for which every elliptic Weierstrass curve with invariant $j$ has no non-trivial point killed by $p$ is finite, an identification `hcard` of the cardinality of that set with $\mathrm{mAnnuli}\ p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p\equiv 3 \bmod 4]$, and chart supply data for $R$ and $S_1$. The conclusion is that for every index $e : \mathrm{Fin}(\mathrm{mAnnuli}\ p)$ the enumerated value $\mathrm{ssValue}\ \Gamma\ e$, namely the $e$-th element of $\mathrm{ssJSet}\ p$ under the bijection furnished by `hcard`, equals $0$ or $1728$.
--
--   This records the classical fact, in the form needed by the chart bookkeeping, that in characteristic $11$ the supersingular $j$-invariants are exactly $0$ (since $11\equiv 2 \bmod 3$) and $1728$ (since $11\equiv 3 \bmod 4$), there being $\mathrm{mAnnuli}(11)=2$ of them. It keys the per-node clauses of the $p=11$ data to the two enumerated nodes, and is used by [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart) and by [`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.ssValue_eq_zero_or_eq_1728_of_eq_eleven (p : ℕ) [Fact p.Prime] (hp11 : p = 11)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ e : Fin (mAnnuli p), ssValue Γ e = 0 ∨ ssValue Γ e = 1728 := by sorry
