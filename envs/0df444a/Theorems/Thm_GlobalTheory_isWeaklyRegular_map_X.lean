-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_map_X
-- name    : GlobalTheory.isWeaklyRegular_map_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:28.079994+00:00
-- url     : https://prove2.me/theorems/d9fa84d3-c44b-4b32-b3a1-f3dfb81ef2dc
-- title:
--   Global Theory: is Weakly Regular map X
-- statement:
--   The Global Theory construction uses the is Weakly Regular map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L146-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}

theorem GlobalTheory.isWeaklyRegular_map_X {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) := by sorry
