-- Prove2me | Theorems.Thm_GlobalTheory_finiteIndex_map_of_surjective
-- name    : GlobalTheory.finiteIndex_map_of_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:50.938497+00:00
-- url     : https://prove2.me/theorems/05d7b45f-dabe-49c6-9c63-ff228f9dc9ac
-- title:
--   Global Theory: finite Index map of surjective
-- statement:
--   The Global Theory construction uses the finite Index map of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L387-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L387-L389

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
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}
variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]
variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}
omit [MeasurableSpace X] [MulAction G X] [MulAction H X] [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G]

theorem GlobalTheory.finiteIndex_map_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ) :
    (K.map φ).FiniteIndex := by sorry
