-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_strip
-- name    : GlobalTheory.CompanionTheory.RgEisGal.Fac_strip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:18.256266+00:00
-- url     : https://prove2.me/theorems/93f776d7-586d-41ed-9463-5360fcce4209
-- title:
--   Rg Eis Gal: Fac strip
-- statement:
--   The Rg Eis Gal construction uses the Fac strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DifferentiableAffLine.lean#L118-L129

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

theorem GlobalTheory.CompanionTheory.RgEisGal.Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by sorry
