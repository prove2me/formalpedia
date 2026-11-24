-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AltSpan_alternatingMap_eq_zero_of_span
-- name    : GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:18:25.906573+00:00
-- url     : https://prove2.me/theorems/7e91ac57-1292-4670-8efa-fc1b34655e74
-- title:
--   Alt Span: alternating Map eq zero of span
-- statement:
--   The Alt Span construction uses the alternating Map eq zero of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AlternatingMapEqZeroOfSpan.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AlternatingMapEqZeroOfSpan.lean#L8-L37

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AltSpan

theorem GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by sorry
