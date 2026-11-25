-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_hasWt_zero_appLE_base
-- name    : GlobalTheory.ZJ.hasWt_zero_appLE_base
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:16.031418+00:00
-- url     : https://prove2.me/theorems/4f7e5f52-38dc-5202-a512-04db9589ff48
-- title:
--   ZJ: has Wt zero app LE base
-- statement:
--   The ZJ construction uses the has Wt zero app LE base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L32-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem GlobalTheory.ZJ.hasWt_zero_appLE_base {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) (a : Γ(S, ⊤)) :
    HasWt i V ((H.hom.appLE ⊤ V le_top).hom a) 0 := by sorry
