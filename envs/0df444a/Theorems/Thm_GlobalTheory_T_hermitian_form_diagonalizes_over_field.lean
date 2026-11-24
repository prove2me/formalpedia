-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_form_diagonalizes_over_field
-- name    : GlobalTheory.T.hermitian_form_diagonalizes_over_field
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:43.71861+00:00
-- url     : https://prove2.me/theorems/56256a8d-b70a-4d55-8e64-f79eb10833e4
-- title:
--   T: hermitian form diagonalizes over field
-- statement:
--   The T construction uses the hermitian form diagonalizes over field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormDiagonalizesOverFieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormDiagonalizesOverFieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverFieldStatement
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

theorem GlobalTheory.T.hermitian_form_diagonalizes_over_field : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) := by sorry
