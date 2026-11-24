-- Prove2me | Theorems.Thm_GlobalTheory_T_invariant_functional_eq_haar_multiple
-- name    : GlobalTheory.T.invariant_functional_eq_haar_multiple
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:54.852278+00:00
-- url     : https://prove2.me/theorems/e7bd5f2d-5614-4c16-9f81-2cf9e9fcd991
-- title:
--   T: invariant functional eq haar multiple
-- statement:
--   The T construction uses the invariant functional eq haar multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultipleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultipleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariant_functional_eq_haar_multiple : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ), (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) → ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by sorry
