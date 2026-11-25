-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_frobeniusClosure
-- name    : GroundTheory.LocalField.Abstract.isClosed_frobeniusClosure
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:10:37.959442+00:00
-- url     : https://prove2.me/theorems/c105597e-2b81-4836-81fb-88fe7502b00d
-- title:
--   Abstract: is Closed frobenius Closure
-- statement:
--   The Abstract construction uses the is Closed frobenius Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L83-L84

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
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
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.LocalField.Abstract.isClosed_frobeniusClosure : IsClosed (frobeniusClosure d L σ : Set G) := by sorry
