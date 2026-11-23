-- Prove2me | Theorems.Thm_GlobalTheory_tupleContraction_apply
-- name    : GlobalTheory.tupleContraction_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:53.501616+00:00
-- url     : https://prove2.me/theorems/43269b37-0bac-4701-9387-91ceeffdbcf3
-- title:
--   Global Theory: tuple Contraction apply
-- statement:
--   The Global Theory construction uses the tuple Contraction apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TupleDifferentialTupleDifferential.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TupleDifferentialTupleDifferential.lean#L38-L39

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
variable (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]
variable {R N}

theorem GlobalTheory.tupleContraction_apply (a : X) (n : ℕ) (f : (Fin (n + 1) → X) →₀ N)
    (x : Fin n → X) : tupleContraction R N a n f x = f (Fin.cons a x) := by sorry

attribute [defeq] GlobalTheory.tupleContraction_apply
