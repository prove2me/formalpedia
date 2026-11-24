-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_jG_mem_rat
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_rat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:13.460816+00:00
-- url     : https://prove2.me/theorems/cec22ea2-e8ad-48ad-a03f-b4587e3ec847
-- title:
--   Rg Eis Levi: j G mem rat
-- statement:
--   The Rg Eis Levi construction uses the j G mem rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L208-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L208-L222

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_rat (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (m : GL ι R)
    (hm : m ∈ A.ratGL ι) : jG A.σ m ∈ A.ratGL (ι ⊕ ι) := by sorry
