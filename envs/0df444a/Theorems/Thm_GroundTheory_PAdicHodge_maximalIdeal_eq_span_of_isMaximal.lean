-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_eq_span_of_isMaximal
-- name    : GroundTheory.PAdicHodge.maximalIdeal_eq_span_of_isMaximal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:39.68081+00:00
-- url     : https://prove2.me/theorems/b85324e9-64e2-559e-9356-6fa503306d20
-- title:
--   PAdic Hodge: maximal Ideal eq span of is Maximal
-- statement:
--   The PAdic Hodge construction uses the maximal Ideal eq span of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean#L117-L119

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Ideal WittVector IsLocalRing
variable {B : Type*} [CommRing B]

theorem GroundTheory.PAdicHodge.maximalIdeal_eq_span_of_isMaximal [IsLocalRing B] {π : B} (hmax : (span {π}).IsMaximal) :
    maximalIdeal B = span {π} := by sorry
