-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_mem_stab_inl_iff
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.mem_stab_inl_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:35.293661+00:00
-- url     : https://prove2.me/theorems/b9b0d14e-fcae-4a19-ba2f-5bf3d411f686
-- title:
--   Rg Eis Levi: mem stab inl iff
-- statement:
--   The Rg Eis Levi construction uses the mem stab inl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L103-L112

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

theorem GlobalTheory.CompanionTheory.RgEisLevi.mem_stab_inl_iff (s : Set ι) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι))) :
    q.1 ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) ↔ piP q ∈ stab R s := by sorry
