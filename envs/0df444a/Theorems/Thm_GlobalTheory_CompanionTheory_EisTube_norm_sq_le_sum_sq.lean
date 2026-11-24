-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_norm_sq_le_sum_sq
-- name    : GlobalTheory.CompanionTheory.EisTube.norm_sq_le_sum_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:15.61485+00:00
-- url     : https://prove2.me/theorems/f13e5439-243a-4ef0-8d6d-10a767c6a911
-- title:
--   Eis Tube: norm sq le sum sq
-- statement:
--   The Eis Tube construction uses the norm sq le sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBounded.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBounded.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.norm_sq_le_sum_sq (ι : Type) [Fintype ι] (y : ι → ℝ) :
    ‖y‖ ^ 2 ≤ ∑ i, y i ^ 2 := by sorry
