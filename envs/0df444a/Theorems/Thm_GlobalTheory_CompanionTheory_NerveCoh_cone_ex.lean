-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_cone_ex
-- name    : GlobalTheory.CompanionTheory.NerveCoh.cone_ex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:48.225327+00:00
-- url     : https://prove2.me/theorems/d02e8a1d-f765-48e8-8991-7c9b8fddfe80
-- title:
--   Nerve Coh: cone ex
-- statement:
--   The Nerve Coh construction uses the cone ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L785-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L785-L795

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

theorem GlobalTheory.CompanionTheory.NerveCoh.cone_ex [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) :
    ∀ τ : Tr R C D, (∀ T j, (τ.aug T).Ex j) → (cone τ.pull).Ex k := by sorry
