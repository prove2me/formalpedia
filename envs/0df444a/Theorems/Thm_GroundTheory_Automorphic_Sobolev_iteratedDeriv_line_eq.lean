-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_iteratedDeriv_line_eq
-- name    : GroundTheory.Automorphic.Sobolev.iteratedDeriv_line_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:04.568829+00:00
-- url     : https://prove2.me/theorems/4428a729-b098-4d77-99f0-950585c94160
-- title:
--   Sobolev: iterated Deriv line eq
-- statement:
--   The Sobolev construction uses the iterated Deriv line eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L33-L45

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem GroundTheory.Automorphic.Sobolev.iteratedDeriv_line_eq {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) t =
      iteratedFDeriv ℝ k f (x₀ + t • y) (fun _ ↦ y) := by sorry
