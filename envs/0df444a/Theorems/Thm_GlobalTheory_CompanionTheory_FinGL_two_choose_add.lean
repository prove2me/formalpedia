-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_two_choose_add
-- name    : GlobalTheory.CompanionTheory.FinGL.two_choose_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:20.334578+00:00
-- url     : https://prove2.me/theorems/6a9b9325-cc70-429a-af44-460813deb2e5
-- title:
--   Fin GL: two choose add
-- statement:
--   The Fin GL construction uses the two choose add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L38-L45

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

theorem GlobalTheory.CompanionTheory.FinGL.two_choose_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by sorry
