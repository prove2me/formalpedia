-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_prod_eq_mul
-- name    : GroundTheory.Global.cycHerbrand_prod_eq_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:35.150448+00:00
-- url     : https://prove2.me/theorems/170052bb-1a3c-4663-b2d0-ffec05ba98c7
-- title:
--   Global: cyc Herbrand prod eq mul
-- statement:
--   The Global construction uses the cyc Herbrand prod eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L78-L83

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
variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]
variable [Fintype G]

theorem GroundTheory.Global.cycHerbrand_prod_eq_mul (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by sorry
