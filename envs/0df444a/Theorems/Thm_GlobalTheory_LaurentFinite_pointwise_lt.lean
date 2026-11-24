-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFinite_pointwise_lt
-- name    : GlobalTheory.LaurentFinite.pointwise_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:19.655049+00:00
-- url     : https://prove2.me/theorems/ae028242-2eb8-4656-8c69-38fcfc47f81c
-- title:
--   Laurent Finite: pointwise lt
-- statement:
--   The Laurent Finite construction uses the pointwise lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L18-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L18-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra

theorem GlobalTheory.LaurentFinite.pointwise_lt (j n k : ℤ) (hj : 2 ≤ j) (hn : |n| ≠ j - 1) (hk : |k| ≤ 1)
    (hne : k ≠ cut j n) :
    (2 * j - 2) * (|cut j n| - |k|) < n ^ 2 - (n - cut j n + k) ^ 2 := by sorry
