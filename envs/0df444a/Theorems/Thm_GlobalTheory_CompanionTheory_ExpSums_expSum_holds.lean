-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExpSums_expSum_holds
-- name    : GlobalTheory.CompanionTheory.ExpSums.expSum_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:20.572533+00:00
-- url     : https://prove2.me/theorems/1ab2e241-2f21-4f96-8664-294c9cd04e14
-- title:
--   Exp Sums: exp Sum holds
-- statement:
--   The Exp Sums construction uses the exp Sum holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RegularizedExponentialSum.lean#L26-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RegularizedExponentialSum.lean#L26-L118

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VandermondeSeparation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExpSums

theorem GlobalTheory.CompanionTheory.ExpSums.expSum_holds : PositivityTheory.Rg.BcB.F.ExpSum := by sorry
