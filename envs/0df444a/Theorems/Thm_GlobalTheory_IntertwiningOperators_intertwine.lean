-- Prove2me | Theorems.Thm_GlobalTheory_IntertwiningOperators_intertwine
-- name    : GlobalTheory.IntertwiningOperators.intertwine
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:56.49013+00:00
-- url     : https://prove2.me/theorems/40a2a33a-87b9-41a7-bd94-b82345a365f3
-- title:
--   Intertwining Operators: intertwine
-- statement:
--   The Intertwining Operators construction uses the intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerBis.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerBis.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwiningOperators
open Polynomial

theorem GlobalTheory.IntertwiningOperators.intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by sorry
