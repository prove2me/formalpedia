-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_exists_spanning_tuple
-- name    : GlobalTheory.TupleCone.exists_spanning_tuple
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:54.260709+00:00
-- url     : https://prove2.me/theorems/a8ac9849-97e7-4c6c-8ef2-68e9c3638639
-- title:
--   Tuple Cone: exists spanning tuple
-- statement:
--   The Tuple Cone construction uses the exists spanning tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L319-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L319-L334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
variable (o t) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Finite σ]

theorem GlobalTheory.TupleCone.exists_spanning_tuple (e : ℕ) : ∃ (M : ℕ) (z : Fin (M + 1) → L) (c : σ → Fin (M + 1)),
    Submodule.span o (Set.range z) = piece o t e ∧ ∀ j, z (c j) = t j ^ e := by sorry
