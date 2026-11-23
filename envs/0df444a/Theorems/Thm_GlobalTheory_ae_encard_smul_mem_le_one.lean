-- Prove2me | Theorems.Thm_GlobalTheory_ae_encard_smul_mem_le_one
-- name    : GlobalTheory.ae_encard_smul_mem_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:17.62365+00:00
-- url     : https://prove2.me/theorems/4eceaf7c-4f85-4c89-a049-981d4a8a6d2b
-- title:
--   Global Theory: ae encard smul mem le one
-- statement:
--   The Global Theory construction uses the ae encard smul mem le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L138-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L138-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

theorem GlobalTheory.ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by sorry
