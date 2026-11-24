-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_fc_zero_snoc
-- name    : GlobalTheory.CompanionTheory.NerveCoh.fc_zero_snoc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:09.259971+00:00
-- url     : https://prove2.me/theorems/b40bbf10-7dff-4b36-a20c-88052cf839da
-- title:
--   Nerve Coh: fc zero snoc
-- statement:
--   The Nerve Coh construction uses the fc zero snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L426-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L426-L431

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

theorem GlobalTheory.CompanionTheory.NerveCoh.fc_zero_snoc (c : Fin 1 ⥤ E) (y : E) (f : c.obj (Fin.last 0) ⟶ y) : fc 0 (snoc c y f) = pt y := by sorry
