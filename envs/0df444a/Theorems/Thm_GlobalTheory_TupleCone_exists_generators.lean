-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_exists_generators
-- name    : GlobalTheory.TupleCone.exists_generators
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:43.94042+00:00
-- url     : https://prove2.me/theorems/221c4609-e969-43a4-8879-89e914fecb31
-- title:
--   Tuple Cone: exists generators
-- statement:
--   The Tuple Cone construction uses the exists generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L272-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L272-L312

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

theorem GlobalTheory.TupleCone.exists_generators : ∃ e : ℕ, 0 < e ∧ ∃ N : ℕ → Submodule o L, (∀ q, (N q).FG) ∧
    (∀ q, N q ≤ piece o t q) ∧ (∀ q, e < q → N q = ⊥) ∧ ∀ n, piece o t n ≤
      ⨆ c ∈ Finset.HasAntidiagonal.antidiagonal n, Submodule.span o (Set.range t) ^ c.1 * N c.2 := by sorry
