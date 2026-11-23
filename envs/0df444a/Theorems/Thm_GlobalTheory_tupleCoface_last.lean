-- Prove2me | Theorems.Thm_GlobalTheory_tupleCoface_last
-- name    : GlobalTheory.tupleCoface_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:00.612694+00:00
-- url     : https://prove2.me/theorems/bcc43ce1-503b-4ed1-8119-383fab3b8ebe
-- title:
--   Global Theory: tuple Coface last
-- statement:
--   The Global Theory construction uses the tuple Coface last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TupleDifferentialTupleDifferential.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TupleDifferentialTupleDifferential.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finsupp
open GlobalTheory
variable {X : Type*}

theorem GlobalTheory.tupleCoface_last (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b (Fin.last (n + 1)) x = Fin.snoc x b := by sorry
