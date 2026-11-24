-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_qiso_of_cone
-- name    : GlobalTheory.CompanionTheory.NerveCoh.qiso_of_cone
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:26:45.911808+00:00
-- url     : https://prove2.me/theorems/325b53a2-2e9e-4175-983d-b634b5a19b36
-- title:
--   Nerve Coh: qiso of cone
-- statement:
--   The Nerve Coh construction uses the qiso of cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L824-L839
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L824-L839

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

theorem GlobalTheory.CompanionTheory.NerveCoh.qiso_of_cone {A B : Cx R} (f : Hm A B) (h : ∀ k, (cone f).Ex k) :
    (∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0) ∧
    (∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) ∧
    (∀ n a, A.d (n + 1) a = 0 → ∀ b, B.d n b = f.f (n + 1) a → ∃ y, A.d n y = a) ∧
    (∀ n z, B.d (n + 1) z = 0 → ∃ x y, A.d (n + 1) x = 0 ∧ f.f (n + 1) x - z = B.d n y) := by sorry
