-- Prove2me | Theorems.Thm_GlobalTheory_TraceDetSplit_det_aeval_prod
-- name    : GlobalTheory.TraceDetSplit.det_aeval_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:50.329051+00:00
-- url     : https://prove2.me/theorems/bebf44be-c9f0-41d8-b8ca-6187d890e92c
-- title:
--   Trace Det Split: det aeval prod
-- statement:
--   The Trace Det Split construction uses the det aeval prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceDetSplit

theorem GlobalTheory.TraceDetSplit.det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by sorry
