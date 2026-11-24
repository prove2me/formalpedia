-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_ev_inj
-- name    : GlobalTheory.CompanionTheory.NerveCoh.CoD.ev_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:03.561965+00:00
-- url     : https://prove2.me/theorems/df62a50b-148c-492b-84a7-271b114d2547
-- title:
--   Co D: ev inj
-- statement:
--   The Co D construction uses the ev inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L657-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L657-L660

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
variable {C D : Type} [Category.{0} C] [Category.{0} D]

theorem GlobalTheory.CompanionTheory.NerveCoh.CoD.ev_inj {E : Type} [Category.{0} E] {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R} (A : CoD H B)
    {x : E} {v w : H.obj x} (h : ∀ (y : E) (f : x ⟶ y), A.ev f v = A.ev f w) : v = w := by sorry
