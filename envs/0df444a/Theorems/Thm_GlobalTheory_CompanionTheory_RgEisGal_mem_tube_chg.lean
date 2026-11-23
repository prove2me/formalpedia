-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_tube_chg
-- name    : GlobalTheory.CompanionTheory.RgEisGal.mem_tube_chg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:57.755093+00:00
-- url     : https://prove2.me/theorems/960d2018-f96d-4ff2-84c6-e1d42bb99206
-- title:
--   Rg Eis Gal: mem tube chg
-- statement:
--   The Rg Eis Gal construction uses the mem tube chg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L43-L45

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal

theorem GlobalTheory.CompanionTheory.RgEisGal.mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by sorry
