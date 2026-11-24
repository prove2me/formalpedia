-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_le
-- name    : GroundTheory.LocalField.Abstract.coe_norm_of_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:41.973694+00:00
-- url     : https://prove2.me/theorems/58f8a708-51b5-47f0-9478-1747653c8b72
-- title:
--   Abstract: coe norm of le
-- statement:
--   The Abstract construction uses the coe norm of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L8-L19

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem GroundTheory.LocalField.Abstract.coe_norm_of_le {K L : Subgroup G} (hKL : K ≤ L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) : (norm A K L a : A) = a := by sorry
