-- Prove2me | Theorems.Thm_GlobalTheory_jetWedge_apply
-- name    : GlobalTheory.jetWedge_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:51.742802+00:00
-- url     : https://prove2.me/theorems/87d3a225-cc76-4995-821f-8fa8fda29d04
-- title:
--   Global Theory: jet Wedge apply
-- statement:
--   The Global Theory construction uses the jet Wedge apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

theorem GlobalTheory.jetWedge_apply (ω : M [⋀^Fin D]→ₗ[A] N) (v : Fin (D + 1) → A × M) :
    jetWedge ω v =
      ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * (v i).1) • ω (fun k => (v (i.succAbove k)).2) := by sorry
