-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces
-- name    : ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/1716daf5-a2f6-57e7-bcca-c73b25548082
-- title:
--   Unique place over a supersingular place via q↦ q^{q^2}
-- statement:
--   Let $q$ be a prime with $q\ge 5$, and let $M'$ be a nonzero natural number with $q\nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that the image of $q$ lies in the nonunits of $A$, and write $\kappa$ for the residue field of $A$. Consider, inside the Laurent series field over $\kappa$, the intermediate field $E_0=\kappa(\,\overline{j}_{q},\ \overline{j}_{q^{M'}})$ generated over $\kappa$ by the reduced $j$-expansion `jqModC` and its substitution `jqNModC` at level $M'$, and the intermediate field $E$ generated over $\kappa$ by the ratios of integral forms for the congruence subgroup $\Gamma_H(q^2M')$ attached to $H=\ker\bigl((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times\bigr)$. Assume $E_0\le E$ and that the inclusion $E_0\hookrightarrow E$ is integral. Let $s$ be a place of $E_0$ over $\kappa$ — a valuation subring of $E_0$ containing $\kappa$, not the whole field, whose ring is a principal ideal ring — and assume $s$ lies in `ssPlaces q M' κ`, i.e. $s$ is rational, is an affine geometric place, and its value at `jGeomGen` lies in the set of supersingular $j$-invariants in characteristic $q$. Then there is exactly one place $w$ of $E$ over $\kappa$ with the property that for all $g\in E_0$ and $g'\in E$ whose Laurent expansion is obtained from that of $g$ by the substitution $q\mapsto q^{q^2}$, one has $g$ in the valuation ring of $s$ if and only if $g'$ lies in that of $w$.
--
--   This expresses the total ramification of the reduced full-level (Igusa) function field over a supersingular place of $X_0(M')_\kappa$, but with the place $w$ detecting $s$ through the substitution $q\mapsto q^{q^2}$ on expansions rather than through the plain inclusion, so it is the companion of [`ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces`](thm.html#ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces) for the other Igusa component. It is used in the identification of valuation subrings of the reduced full-level field with Igusa rings, in [`ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing`](thm.html#ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing) and [`ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent`](thm.html#ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve IsLocalRing
open ModularCurve.FullLevel

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      ∀ (g : ↥(modularFunctionFieldC (ResidueField A) M'))
        (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        (g' : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) →
        (g ∈ s.toValuationSubring ↔ g' ∈ w.toValuationSubring) := by sorry
