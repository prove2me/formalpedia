-- Prove2me | Theorems.Thm_GlobalTheory_KerPow_HasGen_of_range
-- name    : GlobalTheory.KerPow.HasGen.of_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:01.339598+00:00
-- url     : https://prove2.me/theorems/2246d160-b0d9-5e5f-b95f-ebc9fa40c828
-- title:
--   Has Gen: of range
-- statement:
--   The Has Gen construction uses the of range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L114-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

theorem GlobalTheory.KerPow.HasGen.of_range {φ : K → (Y ⟶ X)} {ε : K → ℤ} {W : Y.Opens} (H : HasGen L (fun k => W.ι ≫ φ k) ε)
    (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε := by sorry
