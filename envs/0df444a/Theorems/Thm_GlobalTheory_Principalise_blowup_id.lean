-- Prove2me | Theorems.Thm_GlobalTheory_Principalise_blowup_id
-- name    : GlobalTheory.Principalise.blowup_id
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:38.545752+00:00
-- url     : https://prove2.me/theorems/4d22553c-65be-4e3f-8734-50e8a3d6143a
-- title:
--   Principalise: blowup id
-- statement:
--   The Principalise construction uses the blowup id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L56-L57

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
open GlobalTheory.Principalise

theorem GlobalTheory.Principalise.blowup_id {X : Scheme.{0}} {J : X.IdealSheafData} (h : FinalTheorems.EffCartier J) : FinalTheorems.Blowup (𝟙 X) J := by sorry
