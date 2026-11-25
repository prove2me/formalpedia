-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_cj_apply
-- name    : GlobalTheory.CompanionTheory.RgTransfer.cj_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:05.438065+00:00
-- url     : https://prove2.me/theorems/d6471271-e006-4aee-8f89-9a2aa6852859
-- title:
--   Rg Transfer: cj apply
-- statement:
--   The Rg Transfer construction uses the cj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L574-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L574-L575

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']

theorem GlobalTheory.CompanionTheory.RgTransfer.cj_apply (e : A ≃L[ℂ] A') (f : B ≃L[ℂ] B') (T : A' →L[ℂ] B') (x : A) :
    cj e f T x = f.symm (T (e x)) := by sorry
