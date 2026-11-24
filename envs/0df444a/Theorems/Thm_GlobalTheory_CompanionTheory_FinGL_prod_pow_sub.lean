-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_prod_pow_sub
-- name    : GlobalTheory.CompanionTheory.FinGL.prod_pow_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:26.637597+00:00
-- url     : https://prove2.me/theorems/51b38970-92da-48d5-98c7-0b2deb558608
-- title:
--   Fin GL: prod pow sub
-- statement:
--   The Fin GL construction uses the prod pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean#L10-L36

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

theorem GlobalTheory.CompanionTheory.FinGL.prod_pow_sub (q : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      q ^ n.choose 2 * ∏ i ∈ Finset.Icc 1 n, (q ^ i - 1) := by sorry
