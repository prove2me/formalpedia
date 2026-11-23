-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_mul_mem_latR
-- name    : GlobalTheory.CompanionTheory.SW.LatRat.mul_mem_latR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:12.055818+00:00
-- url     : https://prove2.me/theorems/622d93c9-b7fe-47c0-9332-e18e641df336
-- title:
--   Lat Rat: mul mem lat R
-- statement:
--   The Lat Rat construction uses the mul mem lat R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L43-L47

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

theorem GlobalTheory.CompanionTheory.SW.LatRat.mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by sorry
