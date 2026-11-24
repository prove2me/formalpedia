-- Prove2me | Theorems.Thm_GlobalTheory_Principalise_effCartier_comap_of_disjoint
-- name    : GlobalTheory.Principalise.effCartier_comap_of_disjoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:44:26.957187+00:00
-- url     : https://prove2.me/theorems/29ded66b-eb22-4662-bd9f-26026ecfecb8
-- title:
--   Principalise: eff Cartier comap of disjoint
-- statement:
--   The Principalise construction uses the eff Cartier comap of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean#L43-L54

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

theorem GlobalTheory.Principalise.effCartier_comap_of_disjoint {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap g) := by sorry
