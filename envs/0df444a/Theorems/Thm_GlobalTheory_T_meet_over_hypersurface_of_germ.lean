-- Prove2me | Theorems.Thm_GlobalTheory_T_meet_over_hypersurface_of_germ
-- name    : GlobalTheory.T.meet_over_hypersurface_of_germ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:25.615472+00:00
-- url     : https://prove2.me/theorems/8d067dda-5147-432c-9b2e-86ee5c5bdff9
-- title:
--   T: meet over hypersurface of germ
-- statement:
--   The T construction uses the meet over hypersurface of germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGermStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeetOverHypersurfaceOfGermStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGermStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.meet_over_hypersurface_of_germ : FiniteFibreGermIntegral.Statement → IrreducibleGermMeetOverHypersurface.Statement := by sorry
