-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings
-- name    : GlobalTheory.isIso_of_isClosedImmersion_of_thickenings
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:27.968811+00:00
-- url     : https://prove2.me/theorems/edc00137-6e84-4fb9-b810-f2590c4490a8
-- title:
--   Global Theory: is Iso of is Closed Immersion of thickenings
-- statement:
--   The Global Theory construction uses the is Iso of is Closed Immersion of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L206-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L206-L281

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
      ∀ (H : Over (Spec (CommRingCat.of R))) [Flat H.hom] [LocallyOfFiniteType H.hom]
        (_e : 𝟙_ _ ⟶ H), (∀ p, IsIntegral (H.hom.fiber p)) →
        ∀ (Z : Scheme.{0}) (ι : Z ⟶ H.left) [IsClosedImmersion ι],
          (∀ n : ℕ, ∃ l : (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I n H).left ⟶ Z, l ≫ ι = (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG I n H).left) →
            IsIso ι := by sorry
