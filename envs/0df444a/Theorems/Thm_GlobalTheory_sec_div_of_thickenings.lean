-- Prove2me | Theorems.Thm_GlobalTheory_sec_div_of_thickenings
-- name    : GlobalTheory.sec_div_of_thickenings
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:04.458309+00:00
-- url     : https://prove2.me/theorems/2b51ba90-7ae9-41cb-b07b-d6c7f8df68a9
-- title:
--   Global Theory: sec div of thickenings
-- statement:
--   The Global Theory construction uses the sec div of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecDivOfThickenings.lean#L81-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecDivOfThickenings.lean#L81-L136

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData ThickeningDetermines
  ThickeningDivisible

theorem GlobalTheory.sec_div_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ n : ℕ, ∃ t : ∀ j, Γ((thickObj R I n H).left, (fstG I n H).left ⁻¹ᵁ N.U j), ∀ j, ((fstG I n H).left.app _).hom (s.f j) = resTop (Y := (thickObj R I n H).left) _ (scal ((fstG I n H).left ≫ H.hom) r) * t j) → ∃ s' : LB.Sec N, ∀ j, s.f j = resTop _ (scal H.hom r) * s'.f j := by sorry
