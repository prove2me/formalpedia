-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_convex_hp
-- name    : GlobalTheory.CompanionTheory.RgEisGal.convex_hp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:45.707882+00:00
-- url     : https://prove2.me/theorems/44e0a860-a15f-42b9-a120-dfa889d8adcc
-- title:
--   Rg Eis Gal: convex hp
-- statement:
--   The Rg Eis Gal construction uses the convex hp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L68-L78

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

theorem GlobalTheory.CompanionTheory.RgEisGal.convex_hp (α β γ r : ℝ) : Convex ℝ {x : ℝ × ℝ | r < affR α β γ x} := by sorry
