-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_Rep_cube
-- name    : GlobalTheory.PairingLevels.Rep.cube
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:15.78057+00:00
-- url     : https://prove2.me/theorems/3e0060ff-7461-4c77-a9dc-4fdb569e77b0
-- title:
--   Rep: cube
-- statement:
--   The Rep construction uses the cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L109-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}

theorem GlobalTheory.PairingLevels.Rep.cube [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (a b c : Y ⟶ A) :
    Rep L (pt (a * b * c) - pt (a * b) - pt (a * c) - pt (b * c) + pt a + pt b + pt c - pt (1 : Y ⟶ A))
      (fun Z r z J => cubeVal t z J (r ≫ a) (r ≫ b) (r ≫ c)) := by sorry
