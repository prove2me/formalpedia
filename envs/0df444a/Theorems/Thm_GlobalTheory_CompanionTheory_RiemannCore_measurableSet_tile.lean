-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measurableSet_tile
-- name    : GlobalTheory.CompanionTheory.RiemannCore.measurableSet_tile
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:50.762675+00:00
-- url     : https://prove2.me/theorems/8a441d64-6ca1-491a-a776-34114574205b
-- title:
--   Riemann Core: measurable Set tile
-- statement:
--   The Riemann Core construction uses the measurable Set tile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L71-L73

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

theorem GlobalTheory.CompanionTheory.RiemannCore.measurableSet_tile {D : Set G} (hD : MeasurableSet D) (R : Finset G) (l : G) :
    MeasurableSet (tile D R l) := by sorry
