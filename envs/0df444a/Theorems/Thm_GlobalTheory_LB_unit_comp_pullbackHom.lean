-- Prove2me | Theorems.Thm_GlobalTheory_LB_unit_comp_pullbackHom
-- name    : GlobalTheory.LB.unit_comp_pullbackHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:12:43.155817+00:00
-- url     : https://prove2.me/theorems/8a18af13-4f32-4b8d-8e93-55be0c39c3f8
-- title:
--   LB: unit comp pullback Hom
-- statement:
--   The LB construction uses the unit comp pullback Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/BijectiveToPushforwardComp.lean#L222-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/BijectiveToPushforwardComp.lean#L222-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijectiveToPushforwardComp
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable {L : LB X}

theorem GlobalTheory.LB.unit_comp_pullbackHom (L : LB X) (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (toMod L) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom L f) = toPushforward L f := by sorry
