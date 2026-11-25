-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodTrans_transit_ring
-- name    : GlobalTheory.CompanionTheory.SW.GoodTrans.transit_ring
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:27.690863+00:00
-- url     : https://prove2.me/theorems/a780e62e-c599-4ddf-a3cc-9411a53da33f
-- title:
--   Good Trans: transit ring
-- statement:
--   The Good Trans construction uses the transit ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeGramScalarAlmostAll.lean#L11-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeGramScalarAlmostAll.lean#L11-L73

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

theorem GlobalTheory.CompanionTheory.SW.GoodTrans.transit_ring {T : Type} [CommRing T] (O : Subring T) (s : T →+* T)
    (hs : ∀ y ∈ O, s y ∈ O) (hss : ∀ y, s (s y) = y) {M : ℕ} (JT : Matrix (Fin M) (Fin M) T)
    (hJO : ∀ i j, JT i j ∈ O) (hJ : ∀ i j, s (JT j i) = JT i j) (x y : Fin M → T)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (hxy : hform s JT x x = hform s JT y y)
    (w : T) (hw : w ∈ O) (hxw : hform s JT x x * w = 1)
    (hgood : ∀ p β : O, IsUnit β → s β = β → ∃ ε z : O,
      (ε : T) * s ε = 1 ∧ ((β : T) - s ε * p) * z = 1) :
    ∃ g ∈ UJ s JT, (g : Matrix (Fin M) (Fin M) T) *ᵥ x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) T) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) i j ∈ O := by sorry
