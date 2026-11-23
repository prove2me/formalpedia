-- Prove2me | Theorems.Thm_GroundTheory_Global_cycSub_apply
-- name    : GroundTheory.Global.cycSub_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:33.537375+00:00
-- url     : https://prove2.me/theorems/10a70d41-985c-4c07-870a-972777d212d2
-- title:
--   Global: cyc Sub apply
-- statement:
--   The Global construction uses the cyc Sub apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L26-L28

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
variable {G M : Type*} [Group G] [AddCommGroup M]

theorem GroundTheory.Global.cycSub_apply (ρ : Representation ℤ G M) (σ : G) (x : M) :
    cycSub ρ σ x = ρ σ x - x := by sorry

attribute [defeq] GroundTheory.Global.cycSub_apply
