-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_planeForm_isAlt
-- name    : GlobalTheory.Published.SvN.planeForm_isAlt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:53.422888+00:00
-- url     : https://prove2.me/theorems/72b9d6a1-a4e5-48ca-9061-b1bca3f74c21
-- title:
--   Sv N: plane Form is Alt
-- statement:
--   The Sv N construction uses the plane Form is Alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L721-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L721-L721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel

theorem GlobalTheory.Published.SvN.planeForm_isAlt (F : Type) [Field F] : (planeForm F).IsAlt := by sorry
