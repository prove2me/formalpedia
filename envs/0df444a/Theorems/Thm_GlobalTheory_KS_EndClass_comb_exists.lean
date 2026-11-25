-- Prove2me | Theorems.Thm_GlobalTheory_KS_EndClass_comb_exists
-- name    : GlobalTheory.KS.EndClass.comb_exists
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:11.539809+00:00
-- url     : https://prove2.me/theorems/818b6e13-6053-4866-80ab-a05a57813671
-- title:
--   End Class: comb exists
-- statement:
--   The End Class construction uses the comb exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L154-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L154-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}

theorem GlobalTheory.KS.EndClass.comb_exists {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) (y : Z ⟶ Y) (O : Z.Opens) (W₀ : X.Opens) (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀)
    (ν : ∀ W : X.Opens, Γ(X, W) → Γ(Z, O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
    (hν : LocDerK ((O.ι ≫ y) ≫ q) p ((O.ι ≫ y) ≫ m) (fun _ => 0) W₀ (fun W f => pbT O.ι (ν W f) _)) :
    ∃ c : Fin g → Γ(Z, O), ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ν W f =
      ∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := by sorry
