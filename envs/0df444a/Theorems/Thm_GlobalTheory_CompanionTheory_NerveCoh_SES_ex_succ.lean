-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_SES_ex_succ
-- name    : GlobalTheory.CompanionTheory.NerveCoh.SES.ex_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:38.3738+00:00
-- url     : https://prove2.me/theorems/5e0cce4b-cb37-4750-874a-c37902567cbb
-- title:
--   SES: ex succ
-- statement:
--   The SES construction uses the ex succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L53-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L53-L75

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

theorem GlobalTheory.CompanionTheory.NerveCoh.SES.ex_succ {A B C : Cx R} (S : SES A B C) (hB : ∀ k, B.Ex k) {k : ℕ} (hC : C.Ex k) :
    A.Ex (k + 1) := by sorry
