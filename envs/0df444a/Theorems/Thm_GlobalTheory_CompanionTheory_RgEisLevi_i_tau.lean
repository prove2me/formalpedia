-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_i_tau
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.i_tau
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:33.48756+00:00
-- url     : https://prove2.me/theorems/aec6b052-ae15-4061-be9b-e27238b199c0
-- title:
--   Rg Eis Levi: i tau
-- statement:
--   The Rg Eis Levi construction uses the i tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L190-L191

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.i_tau (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (x : E) :
    A.i (tau A hi h x) = A.σ (A.i x) := by sorry
