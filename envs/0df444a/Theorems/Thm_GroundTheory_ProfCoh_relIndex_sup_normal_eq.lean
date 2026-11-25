-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_relIndex_sup_normal_eq
-- name    : GroundTheory.ProfCoh.relIndex_sup_normal_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:15.111538+00:00
-- url     : https://prove2.me/theorems/5aa85db2-501d-4cde-beac-ee26b2b5fe91
-- title:
--   Prof Coh: rel Index sup normal eq
-- statement:
--   The Prof Coh construction uses the rel Index sup normal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L22-L32

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
variable {G : Type*} [Group G]

theorem GroundTheory.ProfCoh.relIndex_sup_normal_eq {X H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hUX : U ≤ X) :
    X.relIndex (H ⊔ U) = X.relIndex H := by sorry
