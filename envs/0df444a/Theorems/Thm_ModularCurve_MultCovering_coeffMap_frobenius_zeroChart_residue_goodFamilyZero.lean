-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_coeffMap_frobenius_zeroChart_residue_goodFamilyZero
-- name    : ModularCurve.MultCovering.coeffMap_frobenius_zeroChart_residue_goodFamilyZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/847dd35e-3051-5a12-900c-257d8241b936
-- title:
--   Frobenius fixes the zero-chart reductions of the good family
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, meaning that $p$ belongs to the nonunits of $A$; write $k = \mathrm{ResidueField}\,A$ and assume $k$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$ (modular polynomial data together with a Kronecker congruence, integrality of the Hecke $\bar\alpha$ and $\bar\beta$ maps, a place specialisation $P$ with a level-one prolongation pair, a set $S_1$ of places, the finite set $W_n$ of supersingular places of `modularFunctionFieldC k 1`, finiteness and cardinality data for the supersingular $j$-set, and a chart supply), and let $\Phi$ be a family context `FamCtx p r` for some $r$, with underlying family data $\Phi$`.toFamData` having members $t_l$. Consider the zero chart `zeroChart Γ`, the transport of `infChart Γ` along the Fricke involution $w_p$ of `modularFunctionFieldBar (1 * p)`, a component chart over $A$ whose residue map lands in `modularFunctionFieldC k 1`, an intermediate field of $k(\!(q)\!)$ generated over $k$ by the $q$-expansions `jqModC k` and `jqNModC k 1`. Assume `hint`: for every index $l$ the rescaled member $\mathrm{goodFamilyZero}\,\Phi\,l = (p^{\mathrm{hasseExp}\,\Phi\,l})^{-1}\, t_l$ lies in the integers of `zeroChart Γ`. Then for each $l \in \mathrm{Fin}\,r$ the Laurent series over $k$ underlying the zero-chart residue of $\mathrm{goodFamilyZero}\,\Phi\,l$ is fixed by `coeffMap` applied to the Frobenius $x \mapsto x^p$ of $k$, i.e. by the coefficientwise $p$-power map on $k(\!(q)\!)$; equivalently all its coefficients lie in the prime field $\mathbb F_p \subseteq k$.
--
--   This is the rationality statement for the reductions, on the zero chart of the two-component semistable covering of $X_0(p)$, of the $p$-adically rescaled members of a good family: their $q$-expansions have coefficients in $\mathbb F_p$. It is used in the construction of unimodular family data with a two-member certificate when a supersingular value vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_coeffMap_frobenius_zeroChart_residue_goodFamilyZero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.coeffMap_frobenius_zeroChart_residue_goodFamilyZero
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (l : Fin r) :
    coeffMap (frobenius (ResidueField ↥A) p)
        ((((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ :
            ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A)))
      = (((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ :
            ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A)) := by sorry
