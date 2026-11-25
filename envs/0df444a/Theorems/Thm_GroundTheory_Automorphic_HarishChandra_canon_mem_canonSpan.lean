-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_canonSpan
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mem_canonSpan
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:22.250111+00:00
-- url     : https://prove2.me/theorems/6e2dfc85-c7d7-428c-a6ac-818e3d53b7cd
-- title:
--   Harish Chandra: canon mem canon Span
-- statement:
--   The Harish Chandra construction uses the canon mem canon Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L223-L225

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.canon_mem_canonSpan {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) : canon m ∈ canonSpan P m.degree m.degree := by sorry
