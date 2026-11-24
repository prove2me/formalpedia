-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_radius_moebius_perturbation_upperHalfPlane
-- name    : GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:38:46.290105+00:00
-- url     : https://prove2.me/theorems/5c62e615-f644-4016-98a3-c90af17d753a
-- title:
--   T: exists radius moebius perturbation upper Half Plane
-- statement:
--   The T construction uses the exists radius moebius perturbation upper Half Plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane : ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → 1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by sorry
