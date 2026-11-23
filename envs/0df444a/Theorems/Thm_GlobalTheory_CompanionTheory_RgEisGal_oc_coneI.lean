-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_oc_coneI
-- name    : GlobalTheory.CompanionTheory.RgEisGal.oc_coneI
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:48.344925+00:00
-- url     : https://prove2.me/theorems/95af7c49-68e1-4699-9fb1-eae415d488de
-- title:
--   Rg Eis Gal: oc cone I
-- statement:
--   The Rg Eis Gal construction uses the oc cone I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L87-L88

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

theorem GlobalTheory.CompanionTheory.RgEisGal.oc_coneI (r : ℝ) : IsOpen (coneI r) ∧ Convex ℝ (coneI r) := by sorry
