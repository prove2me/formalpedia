-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_split
-- name    : GlobalTheory.CompanionTheory.SW.LDL.gram_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:44.839973+00:00
-- url     : https://prove2.me/theorems/93957ef1-7780-4c21-95b7-bf679c902117
-- title:
--   LDL: gram split
-- statement:
--   The LDL construction uses the gram split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L97-L110

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

theorem GlobalTheory.CompanionTheory.SW.LDL.gram_split (hτι : ∀ r, τ (ι r) = ι r) {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) :
    gram ι τ d u = blk τ (ι (d 0)) (fun j => ι (d 0) * headU u j)
      (fun a b => gram ι τ (Fin.tail d) (tailU u) a b + τ (headU u a) * ι (d 0) * headU u b) := by sorry
