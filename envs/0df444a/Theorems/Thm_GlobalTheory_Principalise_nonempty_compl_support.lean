-- Prove2me | Theorems.Thm_GlobalTheory_Principalise_nonempty_compl_support
-- name    : GlobalTheory.Principalise.nonempty_compl_support
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:21.953006+00:00
-- url     : https://prove2.me/theorems/3f5637e0-0c77-4333-9b5f-1769d8ebefde
-- title:
--   Principalise: nonempty compl support
-- statement:
--   The Principalise construction uses the nonempty compl support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L104-L112

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

theorem GlobalTheory.Principalise.nonempty_compl_support {Y : Scheme.{0}} [IsIntegral Y] {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    (I.support.compl : Set Y).Nonempty := by sorry
