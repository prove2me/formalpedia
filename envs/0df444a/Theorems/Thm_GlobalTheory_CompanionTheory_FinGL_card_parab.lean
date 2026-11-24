-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_parab
-- name    : GlobalTheory.CompanionTheory.FinGL.card_parab
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:27.176364+00:00
-- url     : https://prove2.me/theorems/e5a1aef7-0ab8-4732-906c-bac9eb6eafce
-- title:
--   Fin GL: card parab
-- statement:
--   The Fin GL construction uses the card parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L120-L125

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

theorem GlobalTheory.CompanionTheory.FinGL.card_parab : Nat.card (parab K b) =
    Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} *
      ∏ c, Nat.card (GL {i // b i = c} K) := by sorry
