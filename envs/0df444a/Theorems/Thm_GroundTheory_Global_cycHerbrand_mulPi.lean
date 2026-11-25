-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_mulPi
-- name    : GroundTheory.Global.cycHerbrand_mulPi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:42.425838+00:00
-- url     : https://prove2.me/theorems/62a5d04f-56a4-5a6e-bbf6-273738c64a7b
-- title:
--   Global: cyc Herbrand mul Pi
-- statement:
--   The Global construction uses the cyc Herbrand mul Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L155-L159

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
variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]

theorem GroundTheory.Global.cycHerbrand_mulPi [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by sorry
