-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_gs_comp_stalkMap
-- name    : GlobalTheory.ConstFam.gs_comp_stalkMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:27.482802+00:00
-- url     : https://prove2.me/theorems/2aeb43f8-e4fe-59bd-8ec6-d5a92725afab
-- title:
--   Const Fam: gs comp stalk Map
-- statement:
--   The Const Fam construction uses the gs comp stalk Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem GlobalTheory.ConstFam.gs_comp_stalkMap {X Y Z : Scheme.{0}} (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (σ z) ∈ U)
    (a : Γ(X, U)) : gs (σ ≫ r) z U a = (σ.stalkMap z).hom (gs r (σ z) U a) := by sorry
