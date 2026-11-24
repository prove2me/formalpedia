-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_succ
-- name    : GlobalTheory.CompanionTheory.NerveCoh.cone_ex_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:51.474941+00:00
-- url     : https://prove2.me/theorems/4dbad365-9adb-45b1-a2d8-88b1e44f407a
-- title:
--   Nerve Coh: cone ex succ
-- statement:
--   The Nerve Coh construction uses the cone ex succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L138-L147

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

theorem GlobalTheory.CompanionTheory.NerveCoh.cone_ex_succ {A B : Cx R} (f : Hm A B) (k : ℕ) :
    (cone f).Ex (k + 2) ↔ ∀ (a : A.X (k + 2)) (b : B.X (k + 1)), A.d (k + 2) a = 0 →
      f.f (k + 2) a = B.d (k + 1) b →
      ∃ (y : A.X (k + 1)) (z : B.X k), A.d (k + 1) y = a ∧ f.f (k + 1) y - B.d k z = b := by sorry
