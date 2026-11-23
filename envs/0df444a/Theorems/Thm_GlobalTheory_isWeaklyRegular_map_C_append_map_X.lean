-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_map_C_append_map_X
-- name    : GlobalTheory.isWeaklyRegular_map_C_append_map_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:35.889495+00:00
-- url     : https://prove2.me/theorems/a30f1179-3d32-464a-8023-8051799e3bad
-- title:
--   Global Theory: is Weakly Regular map C append map X
-- statement:
--   The Global Theory construction uses the is Weakly Regular map C append map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L121-L134

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

theorem GlobalTheory.isWeaklyRegular_map_C_append_map_X {rs : List R} (hrs : IsWeaklyRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by sorry
