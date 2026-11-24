-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodTrans_mulVec_mem
-- name    : GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:37.999812+00:00
-- url     : https://prove2.me/theorems/cbe606ad-3a75-445d-b2ed-f4bafcf4a20f
-- title:
--   Good Trans: mul Vec mem
-- statement:
--   The Good Trans construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeGramScalarAlmostAll.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeGramScalarAlmostAll.lean#L82-L85

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodTrans

theorem GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem {T : Type} [CommRing T] (O : Subring T) {M : ℕ} (g : Matrix (Fin M) (Fin M) T)
    (hg : ∀ i j, g i j ∈ O) (x : Fin M → T) (hx : ∀ i, x i ∈ O) (i : Fin M) : (g *ᵥ x) i ∈ O := by sorry
