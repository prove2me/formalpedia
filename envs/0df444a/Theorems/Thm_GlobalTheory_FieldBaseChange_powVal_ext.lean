-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_powVal_ext
-- name    : GlobalTheory.FieldBaseChange.powVal_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:12.138705+00:00
-- url     : https://prove2.me/theorems/42acc29f-7e97-5723-a6af-d4c92a02a85d
-- title:
--   Field Base Change: pow Val ext
-- statement:
--   The Field Base Change construction uses the pow Val ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean#L38-L40

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
variable {S : Type} [CommRing S] {X Y Z : Scheme.{0}} {L : LB X} {g : Y ⟶ X} {k : ℤ}
  {π : Y ⟶ Spec (CommRingCat.of S)}

theorem GlobalTheory.FieldBaseChange.powVal_ext (hL : L.IsLB) {a b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))}
    (h : ∀ y i, g y ∈ L.U i → powVal a (𝟙 Y) y i = powVal b (𝟙 Y) y i) : a = b := by sorry
