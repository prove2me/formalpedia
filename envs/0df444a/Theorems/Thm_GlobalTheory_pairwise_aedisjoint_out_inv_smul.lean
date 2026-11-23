-- Prove2me | Theorems.Thm_GlobalTheory_pairwise_aedisjoint_out_inv_smul
-- name    : GlobalTheory.pairwise_aedisjoint_out_inv_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:19.124497+00:00
-- url     : https://prove2.me/theorems/6f72acd0-c9ee-4b47-acf1-390e4136b5d8
-- title:
--   Global Theory: pairwise aedisjoint out inv smul
-- statement:
--   The Global Theory construction uses the pairwise aedisjoint out inv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L182-L186

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
omit [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

theorem GlobalTheory.pairwise_aedisjoint_out_inv_smul (hD : IsFundamentalDomain G D μ) (K : Subgroup G) :
    Pairwise (Function.onFun (AEDisjoint μ) fun q : G ⧸ K => (q.out)⁻¹ • D) := by sorry
