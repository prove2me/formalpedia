-- Prove2me | Theorems.Thm_GlobalTheory_coneExact_id
-- name    : GlobalTheory.coneExact_id
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:59.03897+00:00
-- url     : https://prove2.me/theorems/9c7288f0-a734-5d90-8934-189010c51839
-- title:
--   Global Theory: cone Exact id
-- statement:
--   The Global Theory construction uses the cone Exact id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L102-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory

theorem GlobalTheory.coneExact_id {K : ℕ → Type v} [∀ p, AddCommGroup (K p)] (d : ∀ p, K p →+ K (p + 1)) :
    ConeExact (fun p => d p) (fun p => d p) (fun _ x => x) := by sorry
