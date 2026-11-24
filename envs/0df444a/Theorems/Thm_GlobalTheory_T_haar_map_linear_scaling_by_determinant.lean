-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_map_linear_scaling_by_determinant
-- name    : GlobalTheory.T.haar_map_linear_scaling_by_determinant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:41:42.949156+00:00
-- url     : https://prove2.me/theorems/d5e9890e-7585-4fcd-bfa3-dcb6fce7bfbc
-- title:
--   T: haar map linear scaling by determinant
-- statement:
--   The T construction uses the haar map linear scaling by determinant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMapLinearScalingByDeterminantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMapLinearScalingByDeterminantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_map_linear_scaling_by_determinant : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam → ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by sorry
