-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
-- name    : GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:12.990068+00:00
-- url     : https://prove2.me/theorems/ef9395b9-d2fa-4452-90d6-3b115c267935
-- title:
--   Complex Sets: irreducible Germ Meet Over Hypersurface of finite Fibre Germ Integral
-- statement:
--   The Complex Sets construction uses the irreducible Germ Meet Over Hypersurface of finite Fibre Germ Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGerm.lean#L52-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGerm.lean#L52-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
    (H : FiniteFibreGermIntegral.Statement) : IrreducibleGermMeetOverHypersurface.Statement := by sorry
