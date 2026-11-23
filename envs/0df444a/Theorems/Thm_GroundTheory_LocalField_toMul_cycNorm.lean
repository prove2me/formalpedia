-- Prove2me | Theorems.Thm_GroundTheory_LocalField_toMul_cycNorm
-- name    : GroundTheory.LocalField.toMul_cycNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:38.215798+00:00
-- url     : https://prove2.me/theorems/b134f646-0cfc-4f53-9171-becc98a4c057
-- title:
--   Local Field: to Mul cyc Norm
-- statement:
--   The Local Field construction uses the to Mul cyc Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L12-L15

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

theorem GroundTheory.LocalField.toMul_cycNorm (x : Additive M) :
    (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = tateNorm G M x.toMul := by sorry
