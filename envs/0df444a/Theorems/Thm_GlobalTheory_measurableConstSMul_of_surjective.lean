-- Prove2me | Theorems.Thm_GlobalTheory_measurableConstSMul_of_surjective
-- name    : GlobalTheory.measurableConstSMul_of_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:31.34119+00:00
-- url     : https://prove2.me/theorems/7888acb9-86fb-44f8-8fd6-c892f2d16107
-- title:
--   Global Theory: measurable Const SMul of surjective
-- statement:
--   The Global Theory construction uses the measurable Const SMul of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L312-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L312-L317

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

theorem GlobalTheory.measurableConstSMul_of_surjective [MeasurableConstSMul G X]
    (hφ : Function.Surjective φ) (hφs : ∀ (g : G) (x : X), φ g • x = g • x) :
    MeasurableConstSMul H X := by sorry
