-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_zero_ex
-- name    : GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ex
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:07.658452+00:00
-- url     : https://prove2.me/theorems/a200c9e6-f071-4e0e-b0f3-d88a0cc80d82
-- title:
--   Co D: zero ex
-- statement:
--   The Co D construction uses the zero ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L482-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L482-L492

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
variable {E : Type} [Category.{0} E]
variable [Quiver.IsThin E]
variable {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R}

theorem GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ex (A : CoD H B) (b : ∀ y, B y) :
    ∃ a : MCn H 0, mdn H 0 a = 0 ∧ ∀ y, A.ev (𝟙 y) (a (pt y)) = b y := by sorry
