-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_lin
-- name    : GlobalTheory.FieldBaseChange.isoRelM_lin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:48:34.97184+00:00
-- url     : https://prove2.me/theorems/528d9a39-f9a9-48be-a1ae-5d68e0f6b343
-- title:
--   Field Base Change: iso Rel M lin
-- statement:
--   The Field Base Change construction uses the iso Rel M lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L80-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L80-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
  {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}

theorem GlobalTheory.FieldBaseChange.isoRelM_lin {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)}
    {π' : Y' ⟶ Spec (CommRingCat.of S)} (hπ : h₁ ≫ π₁ = π') (c : S)
    {a a' : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b b' : SecOver π' (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a' (m ≫ f₂) (𝟙 _) b') :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c • a + a' : SecOver π₁ _) (m ≫ f₂) (𝟙 _) (c • b + b' : SecOver π' _) := by sorry
