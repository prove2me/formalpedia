-- Prove2me | Theorems.Thm_GlobalTheory_T_regular_local_ring_normal_domain
-- name    : GlobalTheory.T.regular_local_ring_normal_domain
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:37.35975+00:00
-- url     : https://prove2.me/theorems/876cd7d0-3be5-4ed5-a9cb-c289619c988b
-- title:
--   T: regular local ring normal domain
-- statement:
--   The T construction uses the regular local ring normal domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomainStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomainStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.regular_local_ring_normal_domain : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by sorry
