-- Prove2me | Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mul_mk
-- name    : GroundTheory.Brauer.BrauerGroup.mk_mul_mk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:57.066914+00:00
-- url     : https://prove2.me/theorems/086c28d3-d3f1-47f4-94ef-0c4a4a443c44
-- title:
--   Brauer Group: mk mul mk
-- statement:
--   The Brauer Group construction uses the mk mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L125-L126

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable (K : Type u) [Field K]
variable {K}

theorem GroundTheory.Brauer.BrauerGroup.mk_mul_mk (A B : CSA.{u, u} K) :
    (⟦A⟧ * ⟦B⟧ : BrauerGroup.{u, u} K) = ⟦tensorCSA A B⟧ := by sorry
