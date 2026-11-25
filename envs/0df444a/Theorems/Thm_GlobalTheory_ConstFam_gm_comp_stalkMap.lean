-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_gm_comp_stalkMap
-- name    : GlobalTheory.ConstFam.gm_comp_stalkMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:37.19777+00:00
-- url     : https://prove2.me/theorems/260a96d0-5413-5cc7-8ac3-e0c97c88e3dd
-- title:
--   Const Fam: gm comp stalk Map
-- statement:
--   The Const Fam construction uses the gm comp stalk Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L49-L52

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

theorem GlobalTheory.ConstFam.gm_comp_stalkMap {X Y Z : Scheme.{0}} (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (σ z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (σ ≫ r) z U a = Units.map (σ.stalkMap z).hom.toMonoidHom (gm r (σ z) U a) := by sorry
