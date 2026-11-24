-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_zero
-- name    : GlobalTheory.CompanionTheory.NerveCoh.cone_ex_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:49.197846+00:00
-- url     : https://prove2.me/theorems/a78a180d-9e09-434b-81d1-8f5b47137cf1
-- title:
--   Nerve Coh: cone ex zero
-- statement:
--   The Nerve Coh construction uses the cone ex zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L123-L126

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

theorem GlobalTheory.CompanionTheory.NerveCoh.cone_ex_zero {A B : Cx R} (f : Hm A B) :
    (cone f).Ex 0 ↔ ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0 := by sorry
