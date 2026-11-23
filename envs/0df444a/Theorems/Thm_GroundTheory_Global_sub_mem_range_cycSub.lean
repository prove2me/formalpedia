-- Prove2me | Theorems.Thm_GroundTheory_Global_sub_mem_range_cycSub
-- name    : GroundTheory.Global.sub_mem_range_cycSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:21.874088+00:00
-- url     : https://prove2.me/theorems/af8d1df7-92e5-4c21-9848-b1eafb7bfb66
-- title:
--   Global: sub mem range cyc Sub
-- statement:
--   The Global construction uses the sub mem range cyc Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L51-L69

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
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}

theorem GroundTheory.Global.sub_mem_range_cycSub (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : M) :
    ρ g x - x ∈ (cycSub ρ σ).range := by sorry
