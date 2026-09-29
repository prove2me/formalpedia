-- Prove2me | Theorems.Thm_ModularCurve_inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField
-- name    : ModularCurve.inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/1ebc2461-a74f-5db5-8673-848dbff4683b
-- title:
--   Valuation ring of the inertia field inside A
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $p$ a nonunit of $A$ (the predicate `LiesOverPrime`), let $k$ be a field of characteristic $p$ and let $\mathrm{red} : A \to k$ be a surjective ring homomorphism. Write $I =$ `A.inertiaSubgroupIn ℚ` for the image of the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ under the inclusion of the decomposition subgroup, $L$ for the fixed field of $I$, and $O = A \cap L$ for the preimage of $A$ under $L \hookrightarrow \overline{\mathbb{Q}}$. The assertion is the existence of a ring homomorphism $\mathrm{incl} : O \to A$ such that: (i) the image of $\mathrm{incl}(o)$ in $\overline{\mathbb{Q}}$ is the image of $o$ under $L \hookrightarrow \overline{\mathbb{Q}}$; (ii) $(\mathrm{red} \circ \mathrm{incl})(o)$ equals $\mathrm{red}$ applied to the element of $A$ given by the image of $o$, transported through the identity ring equivalence of $O$; (iii) $\mathrm{incl}$ followed by $A \hookrightarrow \overline{\mathbb{Q}}$ equals the map $\tau : O \to \overline{\mathbb{Q}}$ obtained from the identity equivalence of $O$, the inclusion $O \hookrightarrow L$ and $L \hookrightarrow \overline{\mathbb{Q}}$; (iv) $\tau$ is injective; (v) $\tau$ extends to a ring homomorphism $\tau_F : \mathrm{Frac}(O) \to \overline{\mathbb{Q}}$ with $\tau_F \circ \mathrm{algebraMap} = \tau$; (vi) $\mathrm{red} \circ \mathrm{incl}$ is surjective; and (vii) the residue field of the local ring $O$ is algebraically closed.
--
--   This records the standard relation between a place $A$ of $\overline{\mathbb{Q}}$ above $p$ and the valuation ring of its inertia field: the inclusion of valuation rings induces an isomorphism on residue fields, which are algebraically closed. It is the bookkeeping input used when assembling Deligne–Rapoport model packages over the inertia field, and is cited by the results producing scheme morphisms over $O$ and the resolved model packages at a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in

theorem ModularCurve.inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    {k : Type} [Field k] [CharP k p] (red : ↥A →+* k) (hred : Function.Surjective red) :
    ∃ incl : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* ↥A,
      (∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((incl o : ↥A) : AlgebraicClosure ℚ) = algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (o : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))) ∧
      (∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), (red.comp incl) o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        (((RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), ((RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) o).2⟩) ∧
      (A.subtype).comp incl = ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
      (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom))) ∧
      Function.Injective ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
      (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom))) ∧
      (∃ τF : FractionRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* AlgebraicClosure ℚ,
        τF.comp (algebraMap ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (FractionRing ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))) = ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
      (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom)))) ∧
      Function.Surjective (red.comp incl) ∧
      IsAlgClosed (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) := by sorry
