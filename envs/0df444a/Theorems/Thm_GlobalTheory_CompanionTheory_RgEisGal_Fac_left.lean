-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left
-- name    : GlobalTheory.CompanionTheory.RgEisGal.Fac_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:48.860004+00:00
-- url     : https://prove2.me/theorems/8c08dcec-1e4d-492a-bc7d-3e93bb05b38c
-- title:
--   Rg Eis Gal: Fac left
-- statement:
--   The Rg Eis Gal construction uses the Fac left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L101-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L101-L116

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.RgEisGal.Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by sorry
