-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_tile_disjoint
-- name    : GlobalTheory.CompanionTheory.RiemannCore.tile_disjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:50.116732+00:00
-- url     : https://prove2.me/theorems/5df9ad91-d188-4fd8-9921-a0336a76f380
-- title:
--   Riemann Core: tile disjoint
-- statement:
--   The Riemann Core construction uses the tile disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L94-L102

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

theorem GlobalTheory.CompanionTheory.RiemannCore.tile_disjoint {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    Pairwise (Function.onFun Disjoint fun l : Λ => tile D R (l : G)) := by sorry
