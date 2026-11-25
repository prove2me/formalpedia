-- Prove2me | Theorems.Thm_GlobalTheory_LB_pullbackIso_hom
-- name    : GlobalTheory.LB.pullbackIso_hom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:24:36.512038+00:00
-- url     : https://prove2.me/theorems/a6ec0ec7-7c56-521b-9351-0be462e19887
-- title:
--   LB: pullback Iso hom
-- statement:
--   The LB construction uses the pullback Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/BijectiveToPushforwardComp.lean#L219-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/BijectiveToPushforwardComp.lean#L219-L220

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

theorem GlobalTheory.LB.pullbackIso_hom (hL : L.IsLB) (f : Y ⟶ X) :
    (pullbackIso hL f).hom = pullbackHom L f := by sorry

attribute [defeq] GlobalTheory.LB.pullbackIso_hom
