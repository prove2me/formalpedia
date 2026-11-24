-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_rs_pb
-- name    : GlobalTheory.AbLaw.H1Iso.rs_pb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:09.765801+00:00
-- url     : https://prove2.me/theorems/529c1e32-43fa-45df-827b-cdf8766312fe
-- title:
--   H1 Iso: rs pb
-- statement:
--   The H1 Iso construction uses the rs pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L22-L26

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

theorem GlobalTheory.AbLaw.H1Iso.rs_pb (f : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (x : Γ(X, U)) : rs Y h' (pb f h x) = pb f (h'.trans h) x := by sorry
