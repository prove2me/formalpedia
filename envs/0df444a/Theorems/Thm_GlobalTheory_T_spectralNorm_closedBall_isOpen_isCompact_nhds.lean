-- Prove2me | Theorems.Thm_GlobalTheory_T_spectralNorm_closedBall_isOpen_isCompact_nhds
-- name    : GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:32.755309+00:00
-- url     : https://prove2.me/theorems/435b1972-dc47-4935-aae5-ae2f6e31bedf
-- title:
--   T: spectral Norm closed Ball is Open is Compact nhds
-- statement:
--   The T construction uses the spectral Norm closed Ball is Open is Compact nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by sorry
