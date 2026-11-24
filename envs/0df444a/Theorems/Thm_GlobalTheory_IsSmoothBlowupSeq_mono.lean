-- Prove2me | Theorems.Thm_GlobalTheory_IsSmoothBlowupSeq_mono
-- name    : GlobalTheory.IsSmoothBlowupSeq.mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:13.568905+00:00
-- url     : https://prove2.me/theorems/5d3d9f9d-a30b-45be-8011-562049a986d8
-- title:
--   Is Smooth Blowup Seq: mono
-- statement:
--   The Is Smooth Blowup Seq construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L23-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

theorem GlobalTheory.IsSmoothBlowupSeq.mono {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B B' : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (hB : B ⊆ B') : _root_.GlobalTheory.IsSmoothBlowupSeq f B' s := by sorry
