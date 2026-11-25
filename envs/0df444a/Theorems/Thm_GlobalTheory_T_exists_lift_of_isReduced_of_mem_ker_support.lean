-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lift_of_isReduced_of_mem_ker_support
-- name    : GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:47.820026+00:00
-- url     : https://prove2.me/theorems/f3a07047-7c52-4c03-9d44-e4b75c2b7e8d
-- title:
--   T: exists lift of is Reduced of mem ker support
-- statement:
--   The T construction uses the exists lift of is Reduced of mem ker support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftOfReducedOfSupportStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftOfReducedOfSupportStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftOfReducedOfSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftOfReducedOfSupportStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by sorry
