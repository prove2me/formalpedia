-- Prove2me | Theorems.Thm_GroundTheory_Global_mul_sup_eq_of_le
-- name    : GroundTheory.Global.mul_sup_eq_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:16.192958+00:00
-- url     : https://prove2.me/theorems/ee3884c7-c06f-4c7f-8c63-65956b158566
-- title:
--   Global: mul sup eq of le
-- statement:
--   The Global construction uses the mul sup eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NonvanishingDivisorSum.lean#L45-L52

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.mul_sup_eq_of_le {R : Type*} [CommRing R] {I J B₁ B₂ : Ideal R} (hIJ : I ⊔ J = ⊤)
    (h₁ : I ≤ B₁) (h₂ : J ≤ B₂) : B₁ * B₂ ⊔ I = B₁ := by sorry
