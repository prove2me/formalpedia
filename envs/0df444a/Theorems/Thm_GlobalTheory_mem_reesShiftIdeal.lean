-- Prove2me | Theorems.Thm_GlobalTheory_mem_reesShiftIdeal
-- name    : GlobalTheory.mem_reesShiftIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:13.24583+00:00
-- url     : https://prove2.me/theorems/f9174ea4-4d2d-464d-84fb-36f76a6ba617
-- title:
--   Global Theory: mem rees Shift Ideal
-- statement:
--   The Global Theory construction uses the mem rees Shift Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.mem_reesShiftIdeal {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := by sorry
