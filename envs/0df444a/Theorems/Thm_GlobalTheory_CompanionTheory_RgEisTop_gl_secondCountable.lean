-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_gl_secondCountable
-- name    : GlobalTheory.CompanionTheory.RgEisTop.gl_secondCountable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:45.170431+00:00
-- url     : https://prove2.me/theorems/ffe2dc62-afe4-48cc-b984-75e41603f0c2
-- title:
--   Rg Eis Top: gl second Countable
-- statement:
--   The Rg Eis Top construction uses the gl second Countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L48-L54

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

theorem GlobalTheory.CompanionTheory.RgEisTop.gl_secondCountable [T2Space R] [SecondCountableTopology R] :
    SecondCountableTopology (GL ι R) := by sorry
