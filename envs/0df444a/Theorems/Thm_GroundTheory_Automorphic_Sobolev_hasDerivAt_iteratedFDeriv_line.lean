-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasDerivAt_iteratedFDeriv_line
-- name    : GroundTheory.Automorphic.Sobolev.hasDerivAt_iteratedFDeriv_line
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:54.507093+00:00
-- url     : https://prove2.me/theorems/8f35ffac-b60d-4be2-8f75-c2bbbf8771f4
-- title:
--   Sobolev: has Deriv At iterated FDeriv line
-- statement:
--   The Sobolev construction uses the has Deriv At iterated FDeriv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L15-L31

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

theorem GroundTheory.Automorphic.Sobolev.hasDerivAt_iteratedFDeriv_line {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    HasDerivAt (fun τ : ℝ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y))
      (iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y)) t := by sorry
