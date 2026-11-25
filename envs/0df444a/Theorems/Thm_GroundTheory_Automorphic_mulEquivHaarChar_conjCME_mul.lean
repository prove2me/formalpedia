-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_mul
-- name    : GroundTheory.Automorphic.mulEquivHaarChar_conjCME_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:31:04.501252+00:00
-- url     : https://prove2.me/theorems/2b55d32a-30e1-4d5f-a7c7-d87e4150e81e
-- title:
--   Automorphic: mul Equiv Haar Char conj CME mul
-- statement:
--   The Automorphic construction uses the mul Equiv Haar Char conj CME mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L32-L35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem GroundTheory.Automorphic.mulEquivHaarChar_conjCME_mul (a b : G) :
    mulEquivHaarChar (conjCME (a * b)) =
      mulEquivHaarChar (conjCME a) * mulEquivHaarChar (conjCME b) := by sorry
