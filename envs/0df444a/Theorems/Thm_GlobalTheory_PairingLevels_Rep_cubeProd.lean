-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_Rep_cubeProd
-- name    : GlobalTheory.PairingLevels.Rep.cubeProd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:38.224661+00:00
-- url     : https://prove2.me/theorems/eaf70c85-dae4-4103-8d9b-07fa03df05bd
-- title:
--   Rep: cube Prod
-- statement:
--   The Rep construction uses the cube Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L121-L129

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

theorem GlobalTheory.PairingLevels.Rep.cubeProd [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (x c : Y ⟶ A) (n : ℕ) :
    Rep L (pt (x ^ n * c) - pt c - pt (x ^ n) + pt (1 : Y ⟶ A) + n • (pt x + pt c - pt (x * c) - pt (1 : Y ⟶ A)))
      (fun Z r z J => ∏ i ∈ Finset.range n, cubeVal t z J ((r ≫ x) ^ i) (r ≫ x) (r ≫ c)) := by sorry
