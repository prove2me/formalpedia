-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_exists_ne_aff
-- name    : GlobalTheory.CompanionTheory.RgEisGal.exists_ne_aff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:04.547618+00:00
-- url     : https://prove2.me/theorems/682dfbc5-bbd3-4820-b4bf-9c7dae5058ba
-- title:
--   Rg Eis Gal: exists ne aff
-- statement:
--   The Rg Eis Gal construction uses the exists ne aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L101-L110

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
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

theorem GlobalTheory.CompanionTheory.RgEisGal.exists_ne_aff {f : ℂ → ℂ} (h : ∃ z, f z ≠ 0) (α β γ : ℝ) (hβ : β ≠ 0) :
    ∃ y : ℂ, f (aff α β γ (0, y)) ≠ 0 := by sorry
