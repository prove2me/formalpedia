-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_cardParab
-- name    : GlobalTheory.CompanionTheory.FinGL.cardParab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:32.972265+00:00
-- url     : https://prove2.me/theorems/65e3db6f-6e29-4a21-85be-5456d1dc882a
-- title:
--   Fin GL: card Parab
-- statement:
--   The Fin GL construction uses the card Parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L180-L182

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

theorem GlobalTheory.CompanionTheory.FinGL.cardParab : ReciprocityTheory.Ty.Fin.St.CardParab := by sorry
