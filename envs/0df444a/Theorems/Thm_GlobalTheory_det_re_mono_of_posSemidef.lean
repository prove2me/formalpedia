-- Prove2me | Theorems.Thm_GlobalTheory_det_re_mono_of_posSemidef
-- name    : GlobalTheory.det_re_mono_of_posSemidef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:55.543621+00:00
-- url     : https://prove2.me/theorems/c5ae7c62-a324-4fd0-ba74-32129ba6ae32
-- title:
--   Global Theory: det re mono of pos Semidef
-- statement:
--   The Global Theory construction uses the det re mono of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDetAddEqDetMulDetOneAdd.lean#L75-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDetAddEqDetMulDetOneAdd.lean#L75-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.det_re_mono_of_posSemidef :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef →
      0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧
        (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0) := by sorry
