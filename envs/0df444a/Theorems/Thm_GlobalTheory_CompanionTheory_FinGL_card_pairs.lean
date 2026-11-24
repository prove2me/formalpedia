-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_pairs
-- name    : GlobalTheory.CompanionTheory.FinGL.card_pairs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:47.357699+00:00
-- url     : https://prove2.me/theorems/ef7b9055-16f3-4b61-96d9-57b283813fdd
-- title:
--   Fin GL: card pairs
-- statement:
--   The Fin GL construction uses the card pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L154-L164

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)

theorem GlobalTheory.CompanionTheory.FinGL.card_pairs :
    Fintype.card ι * Fintype.card ι = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      Fintype.card {p : ι × ι // b p.2 < b p.1} + Fintype.card {p : ι × ι // b p.1 = b p.2} := by sorry
