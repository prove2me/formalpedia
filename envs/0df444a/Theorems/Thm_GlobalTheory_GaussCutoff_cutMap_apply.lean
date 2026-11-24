-- Prove2me | Theorems.Thm_GlobalTheory_GaussCutoff_cutMap_apply
-- name    : GlobalTheory.GaussCutoff.cutMap_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:39.876804+00:00
-- url     : https://prove2.me/theorems/0dfb6b73-1e6e-4142-b972-8d96e061c9d0
-- title:
--   Gauss Cutoff: cut Map apply
-- statement:
--   The Gauss Cutoff construction uses the cut Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartz.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartz.lean#L125-L126

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.GaussCutoff
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem GlobalTheory.GaussCutoff.cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := by sorry
