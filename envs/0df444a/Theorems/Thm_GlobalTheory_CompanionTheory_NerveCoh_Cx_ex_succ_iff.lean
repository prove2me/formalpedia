-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff
-- name    : GlobalTheory.CompanionTheory.NerveCoh.Cx.ex_succ_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:44.698991+00:00
-- url     : https://prove2.me/theorems/857a69a3-3f75-44d0-882d-397483f70601
-- title:
--   Cx: ex succ iff
-- statement:
--   The Cx construction uses the ex succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L42-L43

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.NerveCoh.Cx.ex_succ_iff {A : Cx R} {k : ℕ} : A.Ex (k + 1) ↔ ∀ x, A.d (k + 1) x = 0 → ∃ y, A.d k y = x := by sorry
