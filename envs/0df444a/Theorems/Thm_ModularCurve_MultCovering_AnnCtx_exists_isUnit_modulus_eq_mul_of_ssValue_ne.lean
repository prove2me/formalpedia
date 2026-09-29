-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
-- name    : ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/504f8e0b-7cad-5a40-b048-9d9019270a68
-- title:
--   Supersingular annuli with j ≠ 0, 1728 have modulus p
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` (modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the Hecke operators $\bar\alpha,\bar\beta$ at level $1$, a place specialisation $P$ over $A$ with a level-one prolongation pair $R$ and chart supply data, a finite enumeration of the supersingular $j$-set $\mathtt{ssJSet}\,p$ of the residue field of $A$ of cardinality $\mathtt{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$), and let $\Delta$ be an annulus context `AnnCtx` over $\Gamma$, assigning to each index a pair of annuli in the function field $\mathtt{modularFunctionFieldBar}(1 \cdot p)$ with the coherence properties recorded in that structure. Let $e$ be an index in $\mathrm{Fin}(\mathtt{mAnnuli}\,p)$ whose associated supersingular value $\mathtt{ssValue}\,\Gamma\,e$ in the residue field of $A$ is neither $0$ nor $1728$. Then there is a unit $u$ of $A$ such that the modulus of the annulus $\Delta.\mathtt{annIn}\,e = \Delta.\mathtt{An}\,e$, viewed in $\overline{\mathbb{Q}}$, equals $p \cdot u$.
--
--   This records the width-one case of the local structure of the multiplicative covering of $X_0(p)$: at a supersingular point whose $j$-invariant is neither $0$ nor $1728$ the node is of width one, so the annulus glueing the two components has modulus exactly $p$ up to a unit, matching the local equation $xy = p$ of the Deligne–Rapoport model. It is used in the construction of a uniform multiplicative covering together with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (he0 : ssValue Γ e ≠ 0) (he1728 : ssValue Γ e ≠ 1728) :
    ∃ u : ↥A, IsUnit u ∧ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u := by sorry
