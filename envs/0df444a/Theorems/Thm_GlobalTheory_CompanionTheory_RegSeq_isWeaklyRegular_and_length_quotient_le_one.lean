-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_isWeaklyRegular_and_length_quotient_le_one
-- name    : GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:13.210911+00:00
-- url     : https://prove2.me/theorems/aa4bd861-b754-436e-bef0-49b3580f344a
-- title:
--   Reg Seq: is Weakly Regular and length quotient le one
-- statement:
--   The Reg Seq construction uses the is Weakly Regular and length quotient le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L81-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeaklyRegularOfCotangentIndep.lean#L81-L172

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

theorem GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ)
      (a : Fin d → R), ringKrullDim R ≤ d →
      LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
        ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧
        Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by sorry
