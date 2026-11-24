-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pb_pb
-- name    : GlobalTheory.AbLaw.H1Iso.pb_pb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:55.560802+00:00
-- url     : https://prove2.me/theorems/fac3763c-3387-4fda-adb0-af030bcc5aa6
-- title:
--   H1 Iso: pb pb
-- statement:
--   The H1 Iso construction uses the pb pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L46-L51

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

theorem GlobalTheory.AbLaw.H1Iso.pb_pb {f : X ⟶ Y} {e : Y ⟶ X} (hfe : f ≫ e = 𝟙 X) {U W : X.Opens} {V : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ V) (h' : V ≤ e ⁻¹ᵁ U) (x : Γ(X, U)) :
    pb f h (pb e h' x) = rs X (le_of_comp_id hfe h h') x := by sorry
