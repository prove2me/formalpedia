-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_split_cocycle
-- name    : GlobalTheory.SecLift.split_cocycle
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:41.830797+00:00
-- url     : https://prove2.me/theorems/1854d5b2-4c07-4dc8-98ff-9e9ee47a5d2b
-- title:
--   Sec Lift: split cocycle
-- statement:
--   The Sec Lift construction uses the split cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L208-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L208-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
variable {N : LB X} {N' : LB Y} {F : Y ⟶ X}

theorem GlobalTheory.SecLift.split_cocycle {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (H : FirstCohomologyVanishes N') {I : Type}
    (V : I → X.Opens) (cov : ∀ x : X, ∃ a, x ∈ V a) (k : I → N.ι) (k' : I → N'.ι)
    (h : ∀ a, V a ≤ N.U (k a)) (h' : ∀ a, F ⁻¹ᵁ V a ≤ N'.U (k' a))
    (φ : ∀ a b, Γ(Y, F ⁻¹ᵁ (V a ⊓ V b)))
    (hφ : ∀ a b d (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b) (hd : F y ∈ V d),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) +
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hb, hd⟩ (φ b d) =
        gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V d)) ⟨ha, hd⟩ (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, F ⁻¹ᵁ V a), ∀ a b (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) = gr (𝟙 Y) y (F ⁻¹ᵁ V a) ha (ψ a) -
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ V b) hb (ψ b) := by sorry
