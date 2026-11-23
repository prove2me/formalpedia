-- Prove2me | Theorems.Thm_GlobalTheory_alternating_map_sum_smul_eq_det_smul
-- name    : GlobalTheory.alternating_map_sum_smul_eq_det_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:49.664594+00:00
-- url     : https://prove2.me/theorems/cef0723a-6d90-4b6e-b110-3bfef7e616a4
-- title:
--   Global Theory: alternating map sum smul eq det smul
-- statement:
--   The Global Theory construction uses the alternating map sum smul eq det smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L68-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L68-L98

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

theorem GlobalTheory.alternating_map_sum_smul_eq_det_smul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by sorry
