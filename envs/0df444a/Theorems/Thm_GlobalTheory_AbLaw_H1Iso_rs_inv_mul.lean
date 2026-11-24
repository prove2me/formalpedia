-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_rs_inv_mul
-- name    : GlobalTheory.AbLaw.H1Iso.rs_inv_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:08.620061+00:00
-- url     : https://prove2.me/theorems/34c3c197-2920-46c2-a4c7-f2ae10a4f1c9
-- title:
--   H1 Iso: rs inv mul
-- statement:
--   The H1 Iso construction uses the rs inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L125-L127

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

theorem GlobalTheory.AbLaw.H1Iso.rs_inv_mul {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) :
    rs X h (u⁻¹).val * rs X h u.val = 1 := by sorry
