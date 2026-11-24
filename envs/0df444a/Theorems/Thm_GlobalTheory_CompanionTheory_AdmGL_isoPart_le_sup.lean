-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_isoPart_le_sup
-- name    : GlobalTheory.CompanionTheory.AdmGL.isoPart_le_sup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:32.958791+00:00
-- url     : https://prove2.me/theorems/9ff5e69e-e582-45d0-bc88-0b6cf20a549e
-- title:
--   Adm GL: iso Part le sup
-- statement:
--   The Adm GL construction uses the iso Part le sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L41-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalIsoPartOfSimple.lean#L41-L76

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

theorem GlobalTheory.CompanionTheory.AdmGL.isoPart_le_sup {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W) (W' : Submodule ℂ W)
    (hW : ∀ k, W' ≤ W'.comap (ρ k)) :
    isoPart π ρ ≤ isoPart π (ρ.subrepresentation W' hW) ⊔ isoPart π (ρ.quotient W' hW) := by sorry
