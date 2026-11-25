-- Prove2me | Theorems.Thm_GlobalTheory_IsSmoothBlowupSeq_isIso_restrict
-- name    : GlobalTheory.IsSmoothBlowupSeq.isIso_restrict
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:32.126086+00:00
-- url     : https://prove2.me/theorems/4f083ae5-8236-5975-8d04-239e0751bbe6
-- title:
--   Is Smooth Blowup Seq: is Iso restrict
-- statement:
--   The Is Smooth Blowup Seq construction uses the is Iso restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L89-L98

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

theorem GlobalTheory.IsSmoothBlowupSeq.isIso_restrict {S Y Y' : Scheme.{0}} {f : Y ⟶ S}
    {B : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (U : Y.Opens) (hU : ∀ y ∈ U, y ∉ B) : IsIso (s ∣_ U) := by sorry
