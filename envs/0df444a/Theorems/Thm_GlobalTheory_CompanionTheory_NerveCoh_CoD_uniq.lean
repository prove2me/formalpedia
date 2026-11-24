-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_uniq
-- name    : GlobalTheory.CompanionTheory.NerveCoh.CoD.uniq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:34.761178+00:00
-- url     : https://prove2.me/theorems/e12da0ba-e9f2-4b1f-a220-927bed8e3ab2
-- title:
--   Co D: uniq
-- statement:
--   The Co D construction uses the uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L476-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L476-L480

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

theorem GlobalTheory.CompanionTheory.NerveCoh.CoD.uniq (A : CoD H B) (p q : MCn H 0) (hp : mdn H 0 p = 0) (hq : mdn H 0 q = 0)
    (h : ∀ y, A.ev (𝟙 y) (p (pt y)) = A.ev (𝟙 y) (q (pt y))) : p = q := by sorry
