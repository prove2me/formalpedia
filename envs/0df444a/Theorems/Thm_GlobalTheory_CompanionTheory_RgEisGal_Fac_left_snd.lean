-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_Fac_left_snd
-- name    : GlobalTheory.CompanionTheory.RgEisGal.Fac_left_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:43.245868+00:00
-- url     : https://prove2.me/theorems/543bf995-69c3-4574-bb04-4b64cd69b672
-- title:
--   Rg Eis Gal: Fac left snd
-- statement:
--   The Rg Eis Gal construction uses the Fac left snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L202-L205

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

theorem GlobalTheory.CompanionTheory.RgEisGal.Fac_left_snd {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.2 < a) : Fac (fun l => f l.2) Ω := by sorry
