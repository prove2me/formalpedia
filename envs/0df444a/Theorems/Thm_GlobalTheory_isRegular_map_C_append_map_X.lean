-- Prove2me | Theorems.Thm_GlobalTheory_isRegular_map_C_append_map_X
-- name    : GlobalTheory.isRegular_map_C_append_map_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:21.312675+00:00
-- url     : https://prove2.me/theorems/418fba77-287d-4059-aeec-89c3fdc1443e
-- title:
--   Global Theory: is Regular map C append map X
-- statement:
--   The Global Theory construction uses the is Regular map C append map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L136-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L136-L144

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

theorem GlobalTheory.isRegular_map_C_append_map_X {rs : List R} (hrs : RingTheory.Sequence.IsRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by sorry
