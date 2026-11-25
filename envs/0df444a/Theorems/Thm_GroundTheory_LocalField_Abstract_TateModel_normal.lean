-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_TateModel_normal
-- name    : GroundTheory.LocalField.Abstract.TateModel.normal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:10.281248+00:00
-- url     : https://prove2.me/theorems/a36aaa4b-f111-47fe-a0e5-e386f953cb60
-- title:
--   Tate Model: normal
-- statement:
--   The Tate Model construction uses the normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomTransport.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomTransport.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Theorems.Thm_GroundTheory_LocalField_mem_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField (tateNorm invariants mem_invariants TateZero TateNegOne)
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
  (K L : Subgroup G) (Γ : Type*) [Group Γ] (M : Type*) [CommGroup M] [MulDistribMulAction Γ M]
open GroundTheory.LocalField.Abstract.TateModel
variable {A K L Γ M} (T : TateModel A K L Γ M)
include T

theorem GroundTheory.LocalField.Abstract.TateModel.normal : (L.subgroupOf K).Normal := by sorry
