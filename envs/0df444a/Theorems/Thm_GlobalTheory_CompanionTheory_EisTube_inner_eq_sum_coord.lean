-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_inner_eq_sum_coord
-- name    : GlobalTheory.CompanionTheory.EisTube.inner_eq_sum_coord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:42.602874+00:00
-- url     : https://prove2.me/theorems/9daf2e00-ac75-473e-814f-cdfb7a041a7e
-- title:
--   Eis Tube: inner eq sum coord
-- statement:
--   The Eis Tube construction uses the inner eq sum coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionFiniteDim.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionFiniteDim.lean#L12-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
universe u

theorem GlobalTheory.CompanionTheory.EisTube.inner_eq_sum_coord {ι : Type} [Fintype ι] (v w : EuclideanSpace ℝ ι) :
    ⟪v, w⟫ = ∑ i, v i * w i := by sorry
