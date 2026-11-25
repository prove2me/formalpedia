-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ker_cycNorm_ofMulDistribMulAction
-- name    : GroundTheory.LocalField.ker_cycNorm_ofMulDistribMulAction
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:14.78146+00:00
-- url     : https://prove2.me/theorems/71ddd056-e13c-421f-bbe9-2d1a20f48cf1
-- title:
--   Local Field: ker cyc Norm of Mul Distrib Mul Action
-- statement:
--   The Local Field construction uses the ker cyc Norm of Mul Distrib Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L24-L28

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

theorem GroundTheory.LocalField.ker_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).ker = (tateNorm G M).ker.toAddSubgroup := by sorry
