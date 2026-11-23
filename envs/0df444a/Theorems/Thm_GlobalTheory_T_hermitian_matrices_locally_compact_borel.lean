-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_matrices_locally_compact_borel
-- name    : GlobalTheory.T.hermitian_matrices_locally_compact_borel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:43.225277+00:00
-- url     : https://prove2.me/theorems/fe4589c4-12b2-4bf6-8a67-224f978a6e8e
-- title:
--   T: hermitian matrices locally compact borel
-- statement:
--   The T construction uses the hermitian matrices locally compact borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorelStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorelStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
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

theorem GlobalTheory.T.hermitian_matrices_locally_compact_borel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by sorry
