-- Prove2me | Theorems.Thm_GlobalTheory_isFundamentalDomain_iUnion_out_inv_smul
-- name    : GlobalTheory.isFundamentalDomain_iUnion_out_inv_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:19.081187+00:00
-- url     : https://prove2.me/theorems/f62c3ce2-cb9c-4ae4-87dc-7fd65044dee0
-- title:
--   Global Theory: is Fundamental Domain i Union out inv smul
-- statement:
--   The Global Theory construction uses the is Fundamental Domain i Union out inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L190-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L190-L214

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}

theorem GlobalTheory.isFundamentalDomain_iUnion_out_inv_smul (hD : IsFundamentalDomain G D μ)
    (K : Subgroup G) : IsFundamentalDomain K (⋃ q : G ⧸ K, (q.out)⁻¹ • D) μ := by sorry
