-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_index_sup_normal_eq_mul
-- name    : GroundTheory.ProfCoh.index_sup_normal_eq_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:20.848191+00:00
-- url     : https://prove2.me/theorems/ceaf879f-0494-4a3e-8538-3226a15de8bb
-- title:
--   Prof Coh: index sup normal eq mul
-- statement:
--   The Prof Coh construction uses the index sup normal eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OfNatRelIndexSupAntitone.lean#L34-L37

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

theorem GroundTheory.ProfCoh.index_sup_normal_eq_mul {K H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hKH : K ≤ H) :
    (K ⊔ U).index = (H ⊔ U).index * (K ⊔ U).relIndex H := by sorry
