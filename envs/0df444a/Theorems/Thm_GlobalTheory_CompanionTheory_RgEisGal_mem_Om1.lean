-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om1
-- name    : GlobalTheory.CompanionTheory.RgEisGal.mem_Om1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:56.288604+00:00
-- url     : https://prove2.me/theorems/b3f7633e-4bf2-4148-bc8d-3ba032a6e597
-- title:
--   Rg Eis Gal: mem Om1
-- statement:
--   The Rg Eis Gal construction uses the mem Om1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L47-L49

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

theorem GlobalTheory.CompanionTheory.RgEisGal.mem_Om1 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om1 N r ↔ r < N - x.1 ∧ r < x.1 + 2 * x.2 + 2 - N := by sorry
