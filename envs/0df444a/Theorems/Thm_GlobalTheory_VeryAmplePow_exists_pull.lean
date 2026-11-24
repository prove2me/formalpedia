-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_exists_pull
-- name    : GlobalTheory.VeryAmplePow.exists_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:45.123574+00:00
-- url     : https://prove2.me/theorems/57408c1c-be91-4fef-b703-11a65d772241
-- title:
--   Very Ample Pow: exists pull
-- statement:
--   The Very Ample Pow construction uses the exists pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L220-L227

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (l : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE l).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by sorry
