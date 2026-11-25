-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_fubiniSt
-- name    : GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:45.772956+00:00
-- url     : https://prove2.me/theorems/cd4edd61-a341-4952-8009-cbeadc2897fd
-- title:
--   Nerve Coh: fubini St
-- statement:
--   The Nerve Coh construction uses the fubini St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L843-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L843-L862

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
open MainStatements.Hodge

theorem GlobalTheory.CompanionTheory.NerveCoh.fubiniSt : CxSt → FubiniSt := by sorry
