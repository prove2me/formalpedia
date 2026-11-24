-- Prove2me | Theorems.Thm_GlobalTheory_lift_of_reduced_of_support
-- name    : GlobalTheory.lift_of_reduced_of_support
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:33.663518+00:00
-- url     : https://prove2.me/theorems/e8991272-03ca-4ece-a1d0-a095aa024056
-- title:
--   Global Theory: lift of reduced of support
-- statement:
--   The Global Theory construction uses the lift of reduced of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftOfReducedOfSupport.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftOfReducedOfSupport.lean#L6-L19

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftOfReducedOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem GlobalTheory.lift_of_reduced_of_support {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (g : T ⟶ Y) (hg : ∀ t, g t ∈ i.ker.support) : ∃ h : T ⟶ X, h ≫ i = g := by sorry
