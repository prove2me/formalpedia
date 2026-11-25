-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_pow
-- name    : GroundTheory.Automorphic.mulEquivHaarChar_conjCME_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:51.524733+00:00
-- url     : https://prove2.me/theorems/8d52ca39-5861-47ad-9533-17d44be113fa
-- title:
--   Automorphic: mul Equiv Haar Char conj CME pow
-- statement:
--   The Automorphic construction uses the mul Equiv Haar Char conj CME pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L37-L41

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

theorem GroundTheory.Automorphic.mulEquivHaarChar_conjCME_pow (a : G) (n : ℕ) :
    mulEquivHaarChar (conjCME (a ^ n)) = mulEquivHaarChar (conjCME a) ^ n := by sorry
