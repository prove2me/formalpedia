-- Prove2me | Theorems.Thm_GlobalTheory_IntertwinerCoprimeCharpoly_eq_zero_of_intertwine_of_isCoprime_charpoly
-- name    : GlobalTheory.IntertwinerCoprimeCharpoly.eq_zero_of_intertwine_of_isCoprime_charpoly
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:20.52658+00:00
-- url     : https://prove2.me/theorems/7aa21f1c-55ed-4f1f-b278-8d72bf85e020
-- title:
--   Intertwiner Coprime Charpoly: eq zero of intertwine of is Coprime charpoly
-- statement:
--   The Intertwiner Coprime Charpoly construction uses the eq zero of intertwine of is Coprime charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfIntertwineOfIsCoprimeCharpoly.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfIntertwineOfIsCoprimeCharpoly.lean#L24-L36

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

theorem GlobalTheory.IntertwinerCoprimeCharpoly.eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by sorry
