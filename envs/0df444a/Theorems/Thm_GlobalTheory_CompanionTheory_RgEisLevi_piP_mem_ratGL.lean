-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piP_mem_ratGL
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_ratGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:36.043916+00:00
-- url     : https://prove2.me/theorems/06d5032c-45b6-41e7-a36d-8077e6d249fc
-- title:
--   Rg Eis Levi: pi P mem rat GL
-- statement:
--   The Rg Eis Levi construction uses the pi P mem rat GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L193-L206

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_ratGL (A : Ad E R) (hi : Function.Injective A.i) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.ratGL (ι ⊕ ι)) : piP q ∈ A.ratGL ι := by sorry
