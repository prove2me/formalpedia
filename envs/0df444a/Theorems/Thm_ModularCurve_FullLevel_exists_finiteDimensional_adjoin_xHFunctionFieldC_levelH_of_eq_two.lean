-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two
-- name    : ModularCurve.FullLevel.exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/e1adb21b-00d0-5836-b610-b3668dc58809
-- title:
--   Finiteness over a simple subfield of the X_H q-expansion field, q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ lies in the nonunits of $A$. Write $\kappa =$ `ResidueField A` for the residue field of the local ring $A$, set $N = q^2 M'$, and let $H =$ `levelH q M'` be the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, that is the units congruent to $1$ modulo $q$. Consider $E =$ `xHFunctionFieldC κ N H`, the intermediate field of the Laurent series field `LaurentSeries κ` generated over $\kappa$ by the set `intFormRatiosC κ (CohCarrier.GammaH N H)`, where [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(N)$, of the preimage of $H$ under the determinant-type character `gamma0Units N`. The assertion is that there exists $t \in E$ such that $E$ is finite-dimensional over the intermediate field $\kappa(t)$ obtained by adjoining $t$ to $\kappa$ inside $E$.
--
--   This records that the $q$-expansion function field of the modular curve $X_H$ of level $q^2M'$, with $H$ the units congruent to $1$ modulo $q$, taken over the residue field of a valuation ring of $\overline{\mathbb{Q}}$ above $q$, is a finite extension of a simple subextension $\kappa(t)$, so that it is a function field of one variable over $\kappa$. It is the $q=2$ case of the corresponding statement for larger $q$, and feeds the specialisation arguments on the Igusa-tower leg of the semistable-covering construction, among them the lemmas on places, rational floor traces and good points of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ t : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      FiniteDimensional ↥(IntermediateField.adjoin (ResidueField A) ({t} : Set ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := by sorry
