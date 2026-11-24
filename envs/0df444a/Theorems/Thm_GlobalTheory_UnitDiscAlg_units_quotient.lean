-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_units_quotient
-- name    : GlobalTheory.UnitDiscAlg.units_quotient
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:37.960421+00:00
-- url     : https://prove2.me/theorems/7817d3f8-6fdf-4c7c-a3cd-f4eeed2abdbd
-- title:
--   Unit Disc Alg: units quotient
-- statement:
--   The Unit Disc Alg construction uses the units quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitDiscriminantMatrixQuotientIsUnit.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitDiscriminantMatrixQuotientIsUnit.lean#L75-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewtonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecomposeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommutantValuationDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitDiscAlg

theorem GlobalTheory.UnitDiscAlg.units_quotient : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by sorry
