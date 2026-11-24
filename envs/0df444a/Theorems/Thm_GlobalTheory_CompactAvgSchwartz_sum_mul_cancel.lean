-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_sum_mul_cancel
-- name    : GlobalTheory.CompactAvgSchwartz.sum_mul_cancel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:48.673188+00:00
-- url     : https://prove2.me/theorems/b9e5b6f8-0a83-45d7-abf4-9897364a8cbc
-- title:
--   Compact Avg Schwartz: sum mul cancel
-- statement:
--   The Compact Avg Schwartz construction uses the sum mul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L251-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L251-L256

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz

theorem GlobalTheory.CompactAvgSchwartz.sum_mul_cancel {R : Type} [Ring R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : B * A = 1)
    (y : Fin m → Fin n → R) : (fun i j => ∑ c, B i c * ∑ d, A c d * y d j) = y := by sorry
