-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex_of_acyclic
-- name    : GlobalTheory.CompanionTheory.NerveCoh.cone_ex_of_acyclic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:14.34601+00:00
-- url     : https://prove2.me/theorems/4f97c930-b8de-4361-beb1-04316f15bc56
-- title:
--   Nerve Coh: cone ex of acyclic
-- statement:
--   The Nerve Coh construction uses the cone ex of acyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L149-L164

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

theorem GlobalTheory.CompanionTheory.NerveCoh.cone_ex_of_acyclic {A B : Cx R} (f : Hm A B) (hA : ∀ k, A.Ex (k + 1)) (hB : ∀ k, B.Ex (k + 1))
    (h0 : ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0)
    (h1 : ∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) (k : ℕ) : (cone f).Ex k := by sorry
