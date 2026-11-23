-- Prove2me | Theorems.Thm_GlobalTheory_GaussWidths_mem_of_smul
-- name    : GlobalTheory.GaussWidths.mem_of_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:40.286836+00:00
-- url     : https://prove2.me/theorems/890c6c56-573b-460c-87bb-5ebce5107c3c
-- title:
--   Gauss Widths: mem of smul
-- statement:
--   The Gauss Widths construction uses the mem of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L26-L35

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

theorem GlobalTheory.GaussWidths.mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by sorry
