-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_aff_re
-- name    : GlobalTheory.CompanionTheory.RgEisGal.aff_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:12.487135+00:00
-- url     : https://prove2.me/theorems/1723aeb3-e38b-4f71-8a44-e634b3b162c2
-- title:
--   Rg Eis Gal: aff re
-- statement:
--   The Rg Eis Gal construction uses the aff re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L18-L19

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

theorem GlobalTheory.CompanionTheory.RgEisGal.aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by sorry
