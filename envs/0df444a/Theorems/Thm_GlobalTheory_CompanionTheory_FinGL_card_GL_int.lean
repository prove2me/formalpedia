-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_GL_int
-- name    : GlobalTheory.CompanionTheory.FinGL.card_GL_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:38.384326+00:00
-- url     : https://prove2.me/theorems/c2bfa818-6c76-49a0-b2dd-112aaea05200
-- title:
--   Fin GL: card GL int
-- statement:
--   The Fin GL construction uses the card GL int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L49-L60

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

theorem GlobalTheory.CompanionTheory.FinGL.card_GL_int (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1) := by sorry
