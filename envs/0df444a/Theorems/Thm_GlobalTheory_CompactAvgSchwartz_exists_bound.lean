-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_exists_bound
-- name    : GlobalTheory.CompactAvgSchwartz.exists_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:21.284969+00:00
-- url     : https://prove2.me/theorems/05f83b4b-bcbe-42c7-af44-145a59ec6e3d
-- title:
--   Compact Avg Schwartz: exists bound
-- statement:
--   The Compact Avg Schwartz construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L16-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L16-L40

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
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompactAvgSchwartz.exists_bound (L Li : S → V →L[ℝ] V) (hL : Continuous L) (hLi : Continuous Li) (h : ∀ s x, Li s (L s x) = x)
    (f : SchwartzMap V ℂ) (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (L s y)) x‖ ≤ M := by sorry
