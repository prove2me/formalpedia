-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_zero_ext
-- name    : GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:12.960661+00:00
-- url     : https://prove2.me/theorems/6b437e69-91df-4044-b899-1e1a0bed4467
-- title:
--   Co D: zero ext
-- statement:
--   The Co D construction uses the zero ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L470-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L470-L474

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

theorem GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ext (A : CoD H B) (a : MCn H 0) (ha : mdn H 0 a = 0)
    (h0 : ∀ y, A.ev (𝟙 y) (a (pt y)) = 0) : a = 0 := by sorry
