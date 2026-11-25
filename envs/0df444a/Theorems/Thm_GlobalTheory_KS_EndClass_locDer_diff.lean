-- Prove2me | Theorems.Thm_GlobalTheory_KS_EndClass_locDer_diff
-- name    : GlobalTheory.KS.EndClass.locDer_diff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:47.508829+00:00
-- url     : https://prove2.me/theorems/0985c8e1-d5c1-49ca-9f7d-5183fa4734eb
-- title:
--   End Class: loc Der diff
-- statement:
--   The End Class construction uses the loc Der diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L200-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L200-L239

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

theorem GlobalTheory.KS.EndClass.locDer_diff {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₁ W₂ : X.Opens}
    {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂)
    (f : X ⟶ X) (f₀ : Y ⟶ Y) (hp : f ≫ p = p) (hq : f₀ ≫ q = q) (hm : f₀ ≫ m = m ≫ f)
    (t : T ⟶ Y) (ht : ⊤ ≤ t ⁻¹ᵁ m ⁻¹ᵁ W₁) :
    LocDerK ((t ≫ f₀) ≫ q) p ((t ≫ f₀) ≫ m) (fun _ => 0) W₂ (fun W h =>
      pbT t (d₁ (W₁ ⊓ f ⁻¹ᵁ W) (pbT f h _)) _ - pbT (t ≫ f₀) (d₂ W h) _) := by sorry
