-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_C_cons_map_linForm
-- name    : GlobalTheory.isWeaklyRegular_C_cons_map_linForm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:18.927613+00:00
-- url     : https://prove2.me/theorems/8db88ab0-da0e-42b3-a6f3-a3cce9132311
-- title:
--   Global Theory: is Weakly Regular C cons map lin Form
-- statement:
--   The Global Theory construction uses the is Weakly Regular C cons map lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L429-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L429-L434

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

theorem GlobalTheory.isWeaklyRegular_C_cons_map_linForm {r : R} (hr : r ∈ nonZeroDivisors R)
    {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) := by sorry
