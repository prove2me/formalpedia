-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measure_tile
-- name    : GlobalTheory.CompanionTheory.RiemannCore.measure_tile
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:06.355079+00:00
-- url     : https://prove2.me/theorems/0fb99e47-a1d9-47b8-904e-6fa9f8de2975
-- title:
--   Riemann Core: measure tile
-- statement:
--   The Riemann Core construction uses the measure tile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L75-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L75-L92

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

theorem GlobalTheory.CompanionTheory.RiemannCore.measure_tile (μ : Measure G) [μ.IsAddHaarMeasure] {D : Set G} (hD : MeasurableSet D)
    (hD1 : μ D = 1) (R : Finset G) (Λ : AddSubgroup G)
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) (l : G) :
    μ (tile D R l) = (R.card : ENNReal) := by sorry
