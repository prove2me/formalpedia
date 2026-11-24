-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_tripleProduct_map_leftInvariant
-- name    : GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:13.947373+00:00
-- url     : https://prove2.me/theorems/aa31f131-4a1f-4e26-a019-c7e25cc624e2
-- title:
--   Adelic: triple Product map left Invariant
-- statement:
--   The Adelic construction uses the triple Product map left Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMeasureIwasawaDecomposition.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMeasureIwasawaDecomposition.lean#L9-L10

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_Nuabs
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureIwasawaDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic

theorem GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by sorry
