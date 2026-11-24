-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_unit_corner
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.unit_corner
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:17.499332+00:00
-- url     : https://prove2.me/theorems/94e277bd-01d2-49fb-b93a-7bf6d1e56b0c
-- title:
--   Rg Eis Levi: unit corner
-- statement:
--   The Rg Eis Levi construction uses the unit corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L132-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L132-L137

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.unit_corner (Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ)
    (h0 : ∀ r c, Q (Sum.inr r) (Sum.inl c) = 0) : Q.toBlocks₁₁ ∈ Matrix.unitaryGroup ι ℂ := by sorry
