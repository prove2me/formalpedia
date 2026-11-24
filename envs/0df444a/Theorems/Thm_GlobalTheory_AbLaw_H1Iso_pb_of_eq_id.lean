-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pb_of_eq_id
-- name    : GlobalTheory.AbLaw.H1Iso.pb_of_eq_id
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:58.361812+00:00
-- url     : https://prove2.me/theorems/8839523e-41a9-4c6e-9408-301227b33c30
-- title:
--   H1 Iso: pb of eq id
-- statement:
--   The H1 Iso construction uses the pb of eq id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
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
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.AbLaw.H1Iso.pb_of_eq_id (g : X ⟶ X) (hg : g = 𝟙 X) {U W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (h' : W ≤ U)
    (x : Γ(X, U)) : pb g h x = rs X h' x := by sorry
