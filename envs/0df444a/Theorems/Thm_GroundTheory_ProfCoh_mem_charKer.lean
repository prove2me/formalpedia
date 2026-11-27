-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_charKer
-- name    : GroundTheory.ProfCoh.mem_charKer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:18.019314+00:00
-- url     : https://prove2.me/theorems/6fd155dd-cab7-4e1f-965e-d863ff8c92d0
-- title:
--   Prof Coh: mem char Ker
-- statement:
--   The Prof Coh construction uses the mem char Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L80-L82

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation
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
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
variable {G : Type} [Group G]

theorem GroundTheory.ProfCoh.mem_charKer {χ : Additive G →+ AddCircle (1 : ℚ)} {x : G} :
    x ∈ charKer χ ↔ χ (Additive.ofMul x) = 0 := by sorry
