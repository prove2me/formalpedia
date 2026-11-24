-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFinite_abs_cut_le
-- name    : GlobalTheory.LaurentFinite.abs_cut_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:08.338977+00:00
-- url     : https://prove2.me/theorems/51acc7b3-058c-4fa8-828d-e1b84228261e
-- title:
--   Laurent Finite: abs cut le
-- statement:
--   The Laurent Finite construction uses the abs cut le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L9-L16

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

theorem GlobalTheory.LaurentFinite.abs_cut_le (j n : ℤ) : |cut j n| ≤ 1 := by sorry
