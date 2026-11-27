-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_mulProd
-- name    : GroundTheory.Global.cycHerbrand_mulProd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:23.830044+00:00
-- url     : https://prove2.me/theorems/bcd03dd5-14b4-47c3-926e-ca35af32c122
-- title:
--   Global: cyc Herbrand mul Prod
-- statement:
--   The Global construction uses the cyc Herbrand mul Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L128-L134

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleHerbrand_Product
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
noncomputable section
variable {G : Type*} [Group G]
variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]

theorem GroundTheory.Global.cycHerbrand_mulProd (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by sorry
