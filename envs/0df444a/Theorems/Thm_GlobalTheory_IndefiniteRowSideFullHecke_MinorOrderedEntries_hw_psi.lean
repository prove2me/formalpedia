-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_psi
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_psi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:46.364163+00:00
-- url     : https://prove2.me/theorems/80e88157-5f89-4e33-ba84-303df64e4714
-- title:
--   Minor Ordered Entries: hw psi
-- statement:
--   The Minor Ordered Entries construction uses the hw psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L324-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L324-L326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped TensorProduct Kronecker
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Sizes} (P : ι → Entries S)

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_psi (Q : Entries S) (hQ : Q.Good) (i : ℕ) (hi : i < Q.psiPar.length) :
    (hw Q.psiPar i : ℚ) = Q.psiPar[i] - (((Q.psiPar.length : ℚ) - 1) / 2 - i) := by sorry
