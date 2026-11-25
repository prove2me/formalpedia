-- Prove2me | Theorems.Thm_GroundTheory_Global_hasCyclicHerbrand_of_finite
-- name    : GroundTheory.Global.hasCyclicHerbrand_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:58.368387+00:00
-- url     : https://prove2.me/theorems/faeac313-0d97-49c0-a11b-1d7597c7ee81
-- title:
--   Global: has Cyclic Herbrand of finite
-- statement:
--   The Global construction uses the has Cyclic Herbrand of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L117-L125

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
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
variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module.Finite ℤ M]

theorem GroundTheory.Global.hasCyclicHerbrand_of_finite (ρ : Representation ℤ G M) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : HasCyclicHerbrand ρ σ := by sorry
