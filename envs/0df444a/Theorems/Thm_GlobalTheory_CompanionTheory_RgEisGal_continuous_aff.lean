-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_aff
-- name    : GlobalTheory.CompanionTheory.RgEisGal.continuous_aff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:35.758858+00:00
-- url     : https://prove2.me/theorems/86f1d4e9-83a3-4f21-a185-6894dcaf2abf
-- title:
--   Rg Eis Gal: continuous aff
-- statement:
--   The Rg Eis Gal construction uses the continuous aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L26-L27

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

theorem GlobalTheory.CompanionTheory.RgEisGal.continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by sorry
