-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Tr_cone_up
-- name    : GlobalTheory.CompanionTheory.NerveCoh.Tr.cone_up
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:25.493922+00:00
-- url     : https://prove2.me/theorems/a2f5c95d-2f70-481b-adca-0a7c79d7b710
-- title:
--   Tr: cone up
-- statement:
--   The Tr construction uses the cone up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L703-L718
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L703-L718

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
open GlobalTheory.CompanionTheory.NerveCoh.Tr
variable (τ : Tr R C D)

theorem GlobalTheory.CompanionTheory.NerveCoh.Tr.cone_up [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) : (cone τ.up.pull).Ex k := by sorry
