-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_Rep_congr
-- name    : GlobalTheory.PairingLevels.Rep.congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:44.406887+00:00
-- url     : https://prove2.me/theorems/5ad8d667-c021-4181-a5b6-9a0d2e132735
-- title:
--   Rep: congr
-- statement:
--   The Rep construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L79-L81

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
omit [GrpObj A]

theorem GlobalTheory.PairingLevels.Rep.congr (h : Rep L D f) (hD : D = D') (hf : ∀ Z r z J, f Z r z J = f' Z r z J) : Rep L D' f' := by sorry
