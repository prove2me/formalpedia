-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_rmul_one
-- name    : GlobalTheory.CompanionTheory.SW.LatRat.rmul_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:07:35.859965+00:00
-- url     : https://prove2.me/theorems/28b0a2c6-bde1-43f0-a1fb-8eeb3e44e836
-- title:
--   Lat Rat: rmul one
-- statement:
--   The Lat Rat construction uses the rmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L71-L74

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
omit [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.LatRat.rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by sorry
