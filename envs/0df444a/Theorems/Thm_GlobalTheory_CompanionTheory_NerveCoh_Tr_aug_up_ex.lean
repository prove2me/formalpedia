-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Tr_aug_up_ex
-- name    : GlobalTheory.CompanionTheory.NerveCoh.Tr.aug_up_ex
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:33.765687+00:00
-- url     : https://prove2.me/theorems/75c22ab9-83a9-4c6d-899e-d58ff37b3a1b
-- title:
--   Tr: aug up ex
-- statement:
--   The Tr construction uses the aug up ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L687-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L687-L701

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

theorem GlobalTheory.CompanionTheory.NerveCoh.Tr.aug_up_ex [Quiver.IsThin C] [Quiver.IsThin D] (T : C) (k : ℕ) : (τ.up.aug T).Ex k := by sorry
