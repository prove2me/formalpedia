-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_exists_ofList_append_eq_maximalIdeal
-- name    : GlobalTheory.CompanionTheory.RegSeq.exists_ofList_append_eq_maximalIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:32.143503+00:00
-- url     : https://prove2.me/theorems/2429db7d-723d-4cb5-879a-e6aa53fa1663
-- title:
--   Reg Seq: exists of List append eq maximal Ideal
-- statement:
--   The Reg Seq construction uses the exists of List append eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L7-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L7-L70

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

theorem GlobalTheory.CompanionTheory.RegSeq.exists_ofList_append_eq_maximalIdeal {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    ∃ ys : List R, Ideal.ofList (List.ofFn f ++ ys) = maximalIdeal R ∧
      (List.ofFn f ++ ys).length = (maximalIdeal R).spanFinrank := by sorry
