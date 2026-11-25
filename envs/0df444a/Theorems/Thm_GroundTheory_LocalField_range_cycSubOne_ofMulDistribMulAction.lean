-- Prove2me | Theorems.Thm_GroundTheory_LocalField_range_cycSubOne_ofMulDistribMulAction
-- name    : GroundTheory.LocalField.range_cycSubOne_ofMulDistribMulAction
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:57.183537+00:00
-- url     : https://prove2.me/theorems/5fe24cd9-dd5f-43cc-ab99-4b794fee13e4
-- title:
--   Local Field: range cyc Sub One of Mul Distrib Mul Action
-- statement:
--   The Local Field construction uses the range cyc Sub One of Mul Distrib Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
omit [Fintype G]

theorem GroundTheory.LocalField.range_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range =
      (augmentation G M).toAddSubgroup := by sorry
