-- Prove2me | Theorems.Thm_GlobalTheory_GaussWidths_exists_schwartz_gauss_width
-- name    : GlobalTheory.GaussWidths.exists_schwartz_gauss_width
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:21.672671+00:00
-- url     : https://prove2.me/theorems/fcf0bcdc-1d3a-4806-b369-7c1f20cdc37d
-- title:
--   Gauss Widths: exists schwartz gauss width
-- statement:
--   The Gauss Widths construction uses the exists schwartz gauss width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L10-L24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.GaussWidths.exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by sorry
