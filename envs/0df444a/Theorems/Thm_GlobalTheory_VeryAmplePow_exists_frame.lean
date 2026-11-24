-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_exists_frame
-- name    : GlobalTheory.VeryAmplePow.exists_frame
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:43.429328+00:00
-- url     : https://prove2.me/theorems/75070941-76dd-45b2-83fa-4884ef10e4e1
-- title:
--   Very Ample Pow: exists frame
-- statement:
--   The Very Ample Pow construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L239-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L239-L253

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

theorem GlobalTheory.VeryAmplePow.exists_frame {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (w : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin n) (fun _ => w) (fun _ => 1))) (x : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s)
    (x' : Z ⟶ X) (e : x' = x ≫ w) :
    ∃ τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => x') (fun _ => (n : ℤ))), τ.IsGen ∧
      ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → (val τ r z J).val = sval s (r ≫ x) z J := by sorry
