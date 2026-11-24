-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_one
-- name    : GlobalTheory.CompanionTheory.NerveCoh.cone_ex_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:52.159862+00:00
-- url     : https://prove2.me/theorems/946ec345-a8d7-4602-9206-3615219fb381
-- title:
--   Nerve Coh: cone ex one
-- statement:
--   The Nerve Coh construction uses the cone ex one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L128-L136

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

theorem GlobalTheory.CompanionTheory.NerveCoh.cone_ex_one {A B : Cx R} (f : Hm A B) :
    (cone f).Ex 1 ↔ ∀ (a : A.X 1) (b : B.X 0), A.d 1 a = 0 → f.f 1 a = B.d 0 b →
      ∃ y, A.d 0 y = a ∧ f.f 0 y = b := by sorry
