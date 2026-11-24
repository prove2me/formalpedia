-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piP_mem_kGL
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_kGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:13.344646+00:00
-- url     : https://prove2.me/theorems/dec2ad69-c213-455e-967b-4c2fe7bfaf7e
-- title:
--   Rg Eis Levi: pi P mem k GL
-- statement:
--   The Rg Eis Levi construction uses the pi P mem k GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L139-L144

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_kGL (A : Ad E R) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.kGL (ι ⊕ ι)) : piP q ∈ A.kGL ι := by sorry
