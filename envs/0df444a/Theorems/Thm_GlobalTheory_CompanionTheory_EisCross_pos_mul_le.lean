-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisCross_pos_mul_le
-- name    : GlobalTheory.CompanionTheory.EisCross.pos_mul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:01.050872+00:00
-- url     : https://prove2.me/theorems/57b096c7-66b7-4417-90d9-0ad291749182
-- title:
--   Eis Cross: pos mul le
-- statement:
--   The Eis Cross construction uses the pos mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoarseLipschitzExponentialEstimate.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoarseLipschitzExponentialEstimate.lean#L13-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis

theorem GlobalTheory.CompanionTheory.EisCross.pos_mul_le {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (C : Set G) (A : ℝ)
    (hA : ∀ g, ∀ u ∈ C, |l (g * u) - l g| ≤ A) (hc : Conv Δ P l) (y v : G) (hv : v ∈ C) :
    pos Δ P l (y * v) ≤ Real.exp A * pos Δ P l y := by sorry
