-- Prove2me | Theorems.Thm_GlobalTheory_isIso_restrict_of_closedImmersion_near_generic
-- name    : GlobalTheory.isIso_restrict_of_closedImmersion_near_generic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:10.668141+00:00
-- url     : https://prove2.me/theorems/a49b9f2f-fd8c-41fd-96e0-dcc1a4c557d8
-- title:
--   Global Theory: is Iso restrict of closed Immersion near generic
-- statement:
--   The Global Theory construction uses the is Iso restrict of closed Immersion near generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoRestrictOfClosedImmersionNearGeneric.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIsoRestrictOfClosedImmersionNearGeneric.lean#L8-L44

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGeneric
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
open GlobalTheory

theorem GlobalTheory.isIso_restrict_of_closedImmersion_near_generic :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by sorry
