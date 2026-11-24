-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_exists_test_fun
-- name    : GlobalTheory.CompanionTheory.SW.MassTest.exists_test_fun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:20:23.393122+00:00
-- url     : https://prove2.me/theorems/699b4ba3-313d-4989-be8b-0f304b2084c9
-- title:
--   Mass Test: exists test fun
-- statement:
--   The Mass Test construction uses the exists test fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L85-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TestFunctionExists.lean#L85-L105

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MassTest
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.CompanionTheory.SW.MassTest.exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 2 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ ⊤ := by sorry
