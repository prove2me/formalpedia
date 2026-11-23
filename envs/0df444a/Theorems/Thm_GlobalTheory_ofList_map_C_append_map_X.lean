-- Prove2me | Theorems.Thm_GlobalTheory_ofList_map_C_append_map_X
-- name    : GlobalTheory.ofList_map_C_append_map_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:05.592772+00:00
-- url     : https://prove2.me/theorems/1ef49e7d-26a1-449f-bff1-7a2f982941ef
-- title:
--   Global Theory: of List map C append map X
-- statement:
--   The Global Theory construction uses the of List map C append map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L111-L119

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

theorem GlobalTheory.ofList_map_C_append_map_X (rs : List R) (l : List σ) :
    Ideal.ofList (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) =
      (Ideal.ofList rs).map C ⊔ Ideal.span (X '' {x | x ∈ l}) := by sorry
