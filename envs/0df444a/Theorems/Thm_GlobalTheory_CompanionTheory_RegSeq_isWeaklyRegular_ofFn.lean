-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_isWeaklyRegular_ofFn
-- name    : GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_ofFn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:25.430984+00:00
-- url     : https://prove2.me/theorems/10094aac-dfd8-4a80-ad5f-f36a51dbcc75
-- title:
--   Reg Seq: is Weakly Regular of Fn
-- statement:
--   The Reg Seq construction uses the is Weakly Regular of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L72-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing RingTheory.Sequence
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RegSeq

theorem GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_ofFn {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    IsWeaklyRegular R (List.ofFn f) := by sorry
