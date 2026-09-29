-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
-- name    : ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7a093b2b-1449-54e8-bda8-c2443224d643
-- title:
--   Unique place reading a supersingular place at q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M' \ge 1$ be an integer not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that the image of $q$ lies in the nonunits of $A$; write $\kappa$ for the residue field of $A$. Inside the Laurent series field over $\kappa$ consider two intermediate fields: `modularFunctionFieldC` $\kappa$ $M'$, the field generated over $\kappa$ by the reduced $q$-expansion `jqModC` of $j$ and by its image `jqNModC` under the substitution $q \mapsto q^{M'}$, and `xHFunctionFieldC` $\kappa$ $(q^2M')$ $(\mathrm{levelH}\ q\ M')$, the field generated over $\kappa$ by the ratios `intFormRatiosC` attached to the congruence subgroup $\Gamma_H(q^2M')$ with $H$ the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$. Assume the first field is contained in the second and that the inclusion is an integral ring homomorphism. Let $s$ be a place of `modularFunctionFieldC` $\kappa$ $M'$ over $\kappa$ (a valuation subring, not the whole field, containing the image of $\kappa$ and a principal ideal ring) which lies in `ssPlaces` $q$ $M'$ $\kappa$, i.e. $s$ is rational, satisfies `IsAffineGeomPlace`, and its value at `jGeomGen` $\kappa$ $M'$ lies in `ssJSet` $q$ $\kappa$. Then there is exactly one place $w$ of `xHFunctionFieldC` $\kappa$ $(q^2M')$ $(\mathrm{levelH}\ q\ M')$ over $\kappa$ with the following property: whenever $g$ lies in the smaller field, $g'$ in the larger field, and the Laurent series of $g'$ is obtained from that of $g$ by the substitution $q \mapsto q^{q^2}$ (the ring homomorphism `qExpand` $\kappa$ $(q^2)$), one has $g \in s$ if and only if $g' \in w$.
--
--   This is the $q = 2$ case of the statement that each supersingular place of the characteristic-$q$ function field of $X_0(M')$ is read by a unique place of the level-$\Gamma_H(q^2M')$ field through the twist $q \mapsto q^{q^2}$; at $q = 2$ the Igusa covering of degree $(q-1)/2$ degenerates and the two function fields coincide. It feeds the identification of places with the Igusa ring and the descent statements [`ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing_of_eq_two_of_dvd) and [`ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two`](thm.html#ModularCurve.FullLevel.eq_of_valuationSubring_residueField_igusaRing_of_floorTrace_descent_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two.lean

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

theorem ModularCurve.FullLevel.existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
