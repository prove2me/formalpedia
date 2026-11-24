-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measurableSet_cell
-- name    : GlobalTheory.CompanionTheory.RiemannCore.measurableSet_cell
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:13.450806+00:00
-- url     : https://prove2.me/theorems/c9d8ec02-66b2-4121-9d4c-a97fb30b10b6
-- title:
--   Riemann Core: measurable Set cell
-- statement:
--   The Riemann Core construction uses the measurable Set cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScaling.lean#L67-L69

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

theorem GlobalTheory.CompanionTheory.RiemannCore.measurableSet_cell {D : Set G} (hD : MeasurableSet D) (R : Finset G) :
    MeasurableSet (cell D R) := by sorry
