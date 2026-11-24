-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_exists_finite_smooth
-- name    : GlobalTheory.CompanionTheory.SmoothSpread.exists_finite_smooth
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:35.899561+00:00
-- url     : https://prove2.me/theorems/b13e9c79-4812-4825-bdc2-31c986d5a7cb
-- title:
--   Smooth Spread: exists finite smooth
-- statement:
--   The Smooth Spread construction uses the exists finite smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L104-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L104-L155

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

theorem GlobalTheory.CompanionTheory.SmoothSpread.exists_finite_smooth [Algebra.FinitePresentation R₀ B] [Algebra.Smooth R (R ⊗[R₀] B)] :
    ∃ s : Set R, s.Finite ∧ ∀ A : Subalgebra R₀ R, s ⊆ A → Algebra.Smooth A (A ⊗[R₀] B) := by sorry
