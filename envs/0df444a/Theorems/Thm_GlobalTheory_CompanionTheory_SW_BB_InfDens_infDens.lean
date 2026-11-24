-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_InfDens_infDens
-- name    : GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:35.973422+00:00
-- url     : https://prove2.me/theorems/520b1ba6-af90-4a2b-9d3d-7bedd7d8588b
-- title:
--   Inf Dens: inf Dens
-- statement:
--   The Inf Dens construction uses the inf Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanLocalDensityFormula.lean#L77-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanLocalDensityFormula.lean#L77-L180

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianRankOneHomeomorphBase
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanLocalDensityFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.InfDens

theorem GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by sorry
