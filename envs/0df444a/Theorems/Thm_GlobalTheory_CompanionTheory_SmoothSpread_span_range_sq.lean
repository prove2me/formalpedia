-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_span_range_sq
-- name    : GlobalTheory.CompanionTheory.SmoothSpread.span_range_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:28.841843+00:00
-- url     : https://prove2.me/theorems/691b6fe9-4974-484d-af8a-79f2d20dd575
-- title:
--   Smooth Spread: span range sq
-- statement:
--   The Smooth Spread construction uses the span range sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L92-L102

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
variable {R₀ R B : Type} [CommRing R₀] [CommRing R] [CommRing B] [Algebra R₀ R] [Algebra R₀ B]

theorem GlobalTheory.CompanionTheory.SmoothSpread.span_range_sq {P : Type} [CommRing P] {σ : Type} (g : σ → P) :
    Ideal.span (Set.range g) ^ 2 = Ideal.span (Set.range fun p : σ × σ ↦ g p.1 * g p.2) := by sorry
