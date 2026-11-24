-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_convU_of_parLaw
-- name    : GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:30.421479+00:00
-- url     : https://prove2.me/theorems/28cdf19a-c0f6-4419-81e7-2a57a5355bfc
-- title:
--   Unitary Conv: conv U of par Law
-- statement:
--   The Unitary Conv construction uses the conv U of par Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L81-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L81-L117

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw : ParLaw → ConvU := by sorry
