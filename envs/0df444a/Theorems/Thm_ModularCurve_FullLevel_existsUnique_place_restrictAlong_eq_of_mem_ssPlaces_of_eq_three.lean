-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three
-- name    : ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/14279cb8-82b9-5874-930f-46098f4fc837
-- title:
--   Unique place over a supersingular place when q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that the image of $q$ lies in the non-units of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Inside the Laurent series field $\kappa(\!(q)\!)$ consider two intermediate fields over $\kappa$: the field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ generated over $\kappa$ by the Laurent series $\mathrm{jqModC}\,\kappa$ (the reduction of the $q$-expansion of $j$) and its substitution $q\mapsto q^{M'}$, and the field $\mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$, that is $\mathrm{qExpFunctionFieldC}$ for the subgroup $\mathrm{CohCarrier.GammaH}(q^2M')\,H$ of $\mathrm{SL}(2,\mathbb Z)$ attached to $H=\mathrm{levelH}\,q\,M'$, the kernel of the reduction map $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. Assume the first field is contained in the second, $\mathrm{hle}$, and that the inclusion ring homomorphism is integral. Let $s$ be a place of the first field over $\kappa$ — a valuation subring, not all of the field, containing $\kappa$ and a principal ideal ring — lying in $\mathrm{ssPlaces}\,q\,M'\,\kappa$, i.e. $s$ is rational, satisfies $\mathrm{IsAffineGeomPlace}$, and its value at $\mathrm{jGeomGen}\,\kappa\,M'$ lies in $\mathrm{ssJSet}\,q\,\kappa$. Then there is exactly one place $w$ of the second field over $\kappa$ whose restriction along the inclusion (the preimage valuation subring) equals $s$.
--
--   This is the characteristic-$3$ counterpart of the statement that exactly one place of the reduced full-level ($\Gamma_H(q^2M')$) function field lies over each supersingular place of $X_0(M')$ in characteristic $q$; for $q=3$ the assertion holds for every place, because the level extension is trivial. It feeds the identification of the valuation subrings and Igusa-type rings at the reduced full-level component in the $q=3$ case, being cited by the corresponding uniqueness and descent statements there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three.lean

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

theorem ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      w.restrictAlong (IntermediateField.inclusion hle) hint = s := by sorry
