-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left_fst
-- name    : GlobalTheory.CompanionTheory.RgEisGal.Fac_left_fst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:56.036378+00:00
-- url     : https://prove2.me/theorems/39ee2c71-674e-4d73-9414-36bbfaa5a320
-- title:
--   Rg Eis Gal: Fac left fst
-- statement:
--   The Rg Eis Gal construction uses the Fac left fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L197-L200

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
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

theorem GlobalTheory.CompanionTheory.RgEisGal.Fac_left_fst {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.1 < a) : Fac (fun l => f l.1) Ω := by sorry
