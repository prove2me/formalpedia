-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_polyGaussBdd
-- name    : GlobalTheory.CompanionTheory.EisTube.polyGaussBdd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:25.319242+00:00
-- url     : https://prove2.me/theorems/86c73d48-637e-456b-a03e-f27f75b84a86
-- title:
--   Eis Tube: poly Gauss Bdd
-- statement:
--   The Eis Tube construction uses the poly Gauss Bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBounded.lean#L17-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PolynomialTimesGaussianBounded.lean#L17-L52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.polyGaussBdd : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by sorry
