-- Prove2me | Theorems.Thm_GlobalTheory_SectionKernel_exists_sec_of_local
-- name    : GlobalTheory.SectionKernel.exists_sec_of_local
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:50:50.981737+00:00
-- url     : https://prove2.me/theorems/91b4ad3e-a4ff-4e2f-813e-e2160273f441
-- title:
--   Section Kernel: exists sec of local
-- statement:
--   The Section Kernel construction uses the exists sec of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSectionEqMulOfVanishingModElement.lean#L122-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSectionEqMulOfVanishingModElement.lean#L122-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}

theorem GlobalTheory.SectionKernel.exists_sec_of_local {N : LB X} {N₀ : LB Y} (w : LB.Iso N₀ (N.pull j)) (hN₀ : N₀.IsLB)
    (hw : w.IsGen) {I : Type} (V : I → X.Opens) (c : I → N.ι) (hc : ∀ q, V q ≤ N.U (c q))
    (cov : ∀ z : Y, ∃ q, j z ∈ V q) (u : ∀ q, Γ(X, V q))
    (hu : ∀ q q' z, j z ∈ V q → j z ∈ V q' →
      gs j z _ (u q) = (gm j z _ (N.g (c q) (c q'))).val * gs j z _ (u q')) :
    ∃ τ₀ : LB.Sec N₀, ∀ q k' z, j z ∈ V q → z ∈ N₀.U k' →
      (gw w (𝟙 _) z (c q) k').val * gs (𝟙 _) z _ (τ₀.f k') = gs j z _ (u q) := by sorry
