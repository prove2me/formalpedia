-- Prove2me | Theorems.Thm_GlobalTheory_spectralNorm_closedBall_isOpen_isCompact_nhds_basis
-- name    : GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:35.223799+00:00
-- url     : https://prove2.me/theorems/c1e2b83e-c2a2-452e-a67d-9eda667cde87
-- title:
--   Global Theory: spectral Norm closed Ball is Open is Compact nhds basis
-- statement:
--   The Global Theory construction uses the spectral Norm closed Ball is Open is Compact nhds basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl.lean#L6-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl.lean#L6-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by sorry
