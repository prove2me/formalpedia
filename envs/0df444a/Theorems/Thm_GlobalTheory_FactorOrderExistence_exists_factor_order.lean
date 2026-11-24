-- Prove2me | Theorems.Thm_GlobalTheory_FactorOrderExistence_exists_factor_order
-- name    : GlobalTheory.FactorOrderExistence.exists_factor_order
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:36.077177+00:00
-- url     : https://prove2.me/theorems/d162ba37-fcfd-4b28-ba8a-369c1fb60ca9
-- title:
--   Factor Order Existence: exists factor order
-- statement:
--   The Factor Order Existence construction uses the exists factor order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFactorOrder.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFactorOrder.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FactorOrderExistence
open Filter Topology

theorem GlobalTheory.FactorOrderExistence.exists_factor_order {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ}
    (hw : w ∈ U) (hord : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
      (∀ z : ℂ, g z = (z - w) ^ analyticOrderNatAt g w * h z) ∧ h w ≠ (0 : ℂ) := by sorry
