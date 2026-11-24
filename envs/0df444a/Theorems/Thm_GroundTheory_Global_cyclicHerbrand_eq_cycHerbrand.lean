-- Prove2me | Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_cycHerbrand
-- name    : GroundTheory.Global.cyclicHerbrand_eq_cycHerbrand
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:56.951636+00:00
-- url     : https://prove2.me/theorems/07c3d190-9022-43d8-ba59-91ae5438563b
-- title:
--   Global: cyclic Herbrand eq cyc Herbrand
-- statement:
--   The Global construction uses the cyclic Herbrand eq cyc Herbrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/LatticeBridge.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/LatticeBridge.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
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
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.Global.cyclicHerbrand_eq_cycHerbrand {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ := by sorry
