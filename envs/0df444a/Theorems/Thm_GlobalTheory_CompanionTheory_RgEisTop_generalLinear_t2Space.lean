-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_generalLinear_t2Space
-- name    : GlobalTheory.CompanionTheory.RgEisTop.generalLinear_t2Space
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:17.98881+00:00
-- url     : https://prove2.me/theorems/ef3706da-7f96-4b36-a85f-ab8decf95402
-- title:
--   Rg Eis Top: general Linear t2 Space
-- statement:
--   The Rg Eis Top construction uses the general Linear t2 Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L39-L40

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTop
variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.RgEisTop.generalLinear_t2Space [T2Space R] : T2Space (GL ι R) := by sorry
