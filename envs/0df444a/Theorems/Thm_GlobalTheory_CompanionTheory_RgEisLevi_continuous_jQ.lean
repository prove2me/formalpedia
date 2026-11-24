-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_jQ
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.continuous_jQ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:40.564566+00:00
-- url     : https://prove2.me/theorems/5f5a8114-9cb8-450b-a384-dff95c121124
-- title:
--   Rg Eis Levi: continuous j Q
-- statement:
--   The Rg Eis Levi construction uses the continuous j Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L243-L245

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.continuous_jQ (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (hσ : Continuous A.σ) :
    Continuous (jQ A ε h (ι := ι)) := by sorry
