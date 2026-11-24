-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_oH_isOpenEmbedding
-- name    : GlobalTheory.CompanionTheory.SW.LDL.oH_isOpenEmbedding
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:30.917382+00:00
-- url     : https://prove2.me/theorems/4a2241e0-f750-4c0a-b41f-ba832f8d8daf
-- title:
--   LDL: o H is Open Embedding
-- statement:
--   The LDL construction uses the o H is Open Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L285-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L285-L310

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
variable (ι : R →+* K) (τ : K →+* K)
variable {ι τ}
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace K] [IsTopologicalRing K]
variable {ι : R →+* K} {τ : K →+* K}

theorem GlobalTheory.CompanionTheory.SW.LDL.oH_isOpenEmbedding {lev : K → R} (hι : Continuous ι) (hτ : Continuous τ) (hlev : Continuous lev)
    (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) (hlι : ∀ r, lev (ι r) = r)
    (hfix : ∀ y, τ y = y → ∃ r, y = ι r) (hU : IsOpenEmbedding (Units.val : Rˣ → R)) (n : ℕ) :
    IsOpenEmbedding (oH ι τ hττ hτι n) := by sorry
