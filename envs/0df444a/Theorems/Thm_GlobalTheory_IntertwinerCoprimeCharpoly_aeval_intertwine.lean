-- Prove2me | Theorems.Thm_GlobalTheory_IntertwinerCoprimeCharpoly_aeval_intertwine
-- name    : GlobalTheory.IntertwinerCoprimeCharpoly.aeval_intertwine
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:53.425482+00:00
-- url     : https://prove2.me/theorems/f873243b-bd3c-4d72-9b64-d7a2ac088902
-- title:
--   Intertwiner Coprime Charpoly: aeval intertwine
-- statement:
--   The Intertwiner Coprime Charpoly construction uses the aeval intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfIntertwineOfIsCoprimeCharpoly.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfIntertwineOfIsCoprimeCharpoly.lean#L15-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfIntertwineOfIsCoprimeCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwinerCoprimeCharpoly
open Polynomial

theorem GlobalTheory.IntertwinerCoprimeCharpoly.aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by sorry
