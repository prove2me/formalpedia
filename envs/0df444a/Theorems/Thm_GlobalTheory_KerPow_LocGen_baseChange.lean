-- Prove2me | Theorems.Thm_GlobalTheory_KerPow_LocGen_baseChange
-- name    : GlobalTheory.KerPow.LocGen.baseChange
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:05.313981+00:00
-- url     : https://prove2.me/theorems/18bcbbe4-4bfd-5e84-a214-fa0171575b1b
-- title:
--   Loc Gen: base Change
-- statement:
--   The Loc Gen construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L122-L128

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

theorem GlobalTheory.KerPow.LocGen.baseChange {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : LocGen L π φ ε) {π' : Y' ⟶ B'}
    (h : Y' ⟶ Y) (g : B' ⟶ B) (sq : h ≫ π = π' ≫ g) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) :
    LocGen L π' φ' ε := by sorry
