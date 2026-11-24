-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_BaseChange_ap_top_eq_cst
-- name    : GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:44.560691+00:00
-- url     : https://prove2.me/theorems/54bf1587-b1e1-447d-ba44-439d16ec0e75
-- title:
--   Base Change: ap top eq cst
-- statement:
--   The Base Change construction uses the ap top eq cst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsProjByBaseChange.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsProjByBaseChange.lean#L24-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsProjByBaseChange
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.BaseChange

theorem GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by sorry
