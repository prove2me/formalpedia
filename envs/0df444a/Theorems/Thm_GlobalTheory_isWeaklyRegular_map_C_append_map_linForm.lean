-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_map_C_append_map_linForm
-- name    : GlobalTheory.isWeaklyRegular_map_C_append_map_linForm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:26.448332+00:00
-- url     : https://prove2.me/theorems/c8c73f3c-5ebc-408a-b569-6defe462fc0d
-- title:
--   Global Theory: is Weakly Regular map C append map lin Form
-- statement:
--   The Global Theory construction uses the is Weakly Regular map C append map lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L407-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L407-L412

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
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu

theorem GlobalTheory.isWeaklyRegular_map_C_append_map_linForm {rs : List R} (hrs : IsWeaklyRegular R rs)
    {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R)
      (rs.map (C : R →+* MvPolynomial (ι × J) R) ++ l.map (linForm u)) := by sorry
