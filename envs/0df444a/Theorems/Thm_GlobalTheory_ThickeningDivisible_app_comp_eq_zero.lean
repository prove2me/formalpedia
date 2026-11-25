-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningDivisible_app_comp_eq_zero
-- name    : GlobalTheory.ThickeningDivisible.app_comp_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:07.860444+00:00
-- url     : https://prove2.me/theorems/b8e0367f-1a4c-4aaa-9438-42662879dbaa
-- title:
--   Thickening Divisible: app comp eq zero
-- statement:
--   The Thickening Divisible construction uses the app comp eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecDivOfThickenings.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecDivOfThickenings.lean#L35-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed

theorem GlobalTheory.ThickeningDivisible.app_comp_eq_zero {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U)) (t : Γ(Y, a ⁻¹ᵁ U))
    (h : (a.app U).hom f = resTop _ (scal (a ≫ p) r) * t) : ((b ≫ a).app U).hom f = 0 := by sorry
