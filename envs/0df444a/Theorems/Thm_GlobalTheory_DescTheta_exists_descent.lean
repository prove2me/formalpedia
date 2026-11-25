-- Prove2me | Theorems.Thm_GlobalTheory_DescTheta_exists_descent
-- name    : GlobalTheory.DescTheta.exists_descent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:49.084957+00:00
-- url     : https://prove2.me/theorems/0031e6e2-4142-519e-bac5-58296a477d87
-- title:
--   Desc Theta: exists descent
-- statement:
--   The Desc Theta construction uses the exists descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L166-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L166-L211

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}

theorem GlobalTheory.DescTheta.exists_descent {Γ : Type} [Group Γ] [Fintype Γ] {Y' : Scheme.{0}} (τ : Γ →* Aut Y)
    (φ : Y ⟶ Y') (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hq : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    {L : LB Y'} (O : Y'.Opens) (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ O)) :
    ∃ t : Γ(toMod L, O), ∀ i, (φ.app (O ⊓ L.U i)).hom (coord t i) =
      ∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
        (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i))) := by sorry
