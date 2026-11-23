-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_isGen_of_germs
-- name    : GlobalTheory.TorsionFixedAut.isGen_of_germs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:28.650833+00:00
-- url     : https://prove2.me/theorems/715eec30-7d56-4009-b13f-0e446381d342
-- title:
--   Torsion Fixed Aut: is Gen of germs
-- statement:
--   The Torsion Fixed Aut construction uses the is Gen of germs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L19-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
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
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem GlobalTheory.TorsionFixedAut.isGen_of_germs {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (h : ∀ (y : Y) (j j' : K → L.ι), y ∈ LB.wchart L φ j → y ∈ LB.wchart L φ j' →
      gm (𝟙 Y) y (LB.wchart L φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart L φ j') (t.s j')) :
    t.IsGen := by sorry
