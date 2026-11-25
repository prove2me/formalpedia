-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_mdn_modOf
-- name    : GlobalTheory.CompanionTheory.NerveCoh.mdn_modOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:57.775074+00:00
-- url     : https://prove2.me/theorems/d0e9cfc0-22e4-4850-aa4e-48f840c5ad9c
-- title:
--   Nerve Coh: mdn mod Of
-- statement:
--   The Nerve Coh construction uses the mdn mod Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L811-L811
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L811-L811

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
open GlobalTheory.CatCoh MainStatements.Hodge
variable {C D : Type} [Category.{0} C] [Category.{0} D]

theorem GlobalTheory.CompanionTheory.NerveCoh.mdn_modOf (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (f : Cn F n) : mdn (modOf F) n f = dn F n f := by sorry
