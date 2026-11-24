-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_finite_lattice_points
-- name    : GlobalTheory.CompanionTheory.RiemannCore.finite_lattice_points
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:04.762938+00:00
-- url     : https://prove2.me/theorems/d0a0c41a-f353-423a-af86-af43cf57c200
-- title:
--   Riemann Core: finite lattice points
-- statement:
--   The Riemann Core construction uses the finite lattice points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L111-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L111-L139

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

theorem GlobalTheory.CompanionTheory.RiemannCore.finite_lattice_points (μ : Measure G) [μ.IsAddHaarMeasure] {D K₀ : Set G}
    (hD : MeasurableSet D) (hK : IsCompact K₀) (hDK : D ⊆ K₀) (hD1 : μ D = 1) (R : Finset G)
    (Λ : AddSubgroup G) (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D)
    (x0 : G) {C : Set G} (hC : IsCompact C) : {l : Λ | x0 + (l : G) ∈ C}.Finite := by sorry
