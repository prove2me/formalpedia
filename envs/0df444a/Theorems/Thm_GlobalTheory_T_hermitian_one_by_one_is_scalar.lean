-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_one_by_one_is_scalar
-- name    : GlobalTheory.T.hermitian_one_by_one_is_scalar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:42.477723+00:00
-- url     : https://prove2.me/theorems/a4ede35d-303d-4140-bc01-de281b29fe8f
-- title:
--   T: hermitian one by one is scalar
-- statement:
--   The T construction uses the hermitian one by one is scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOneByOneIsScalarStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOneByOneIsScalarStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOneByOneIsScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOneByOneIsScalarStatement
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

theorem GlobalTheory.T.hermitian_one_by_one_is_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by sorry
