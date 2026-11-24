-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_bdet_inl
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:11.822296+00:00
-- url     : https://prove2.me/theorems/3ee91267-ec55-4348-ab6c-4eb617c1956e
-- title:
--   Rg Eis Levi: bdet inl
-- statement:
--   The Rg Eis Levi construction uses the bdet inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L127-L130

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl (s : Set ι) (g : GL (ι ⊕ ι) R) (m : GL ι R)
    (h : ∀ r c, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl r) (Sum.inl c) = (m : Matrix ι ι R) r c) :
    bdet (Sum.inl '' s : Set (ι ⊕ ι)) g = bdet s m := by sorry
