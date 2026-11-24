-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_lmul_apply
-- name    : GlobalTheory.CompactAvgSchwartz.lmul_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:45.273883+00:00
-- url     : https://prove2.me/theorems/47ad8d31-d668-4da7-8261-0b117f744e39
-- title:
--   Compact Avg Schwartz: lmul apply
-- statement:
--   The Compact Avg Schwartz construction uses the lmul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L248-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L248-L249

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

theorem GlobalTheory.CompactAvgSchwartz.lmul_apply {ι : Type} [Fintype ι] {m : ℕ} (n : ℕ) (A : ι → Matrix (Fin m) (Fin m) ℂ) (X : ι → Fin m → Fin n → ℂ) :
    lmul n A X = fun τ i j => ∑ c, A τ i c * X τ c j := by sorry
