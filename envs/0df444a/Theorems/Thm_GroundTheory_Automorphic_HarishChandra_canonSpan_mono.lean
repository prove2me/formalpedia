-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canonSpan_mono
-- name    : GroundTheory.Automorphic.HarishChandra.canonSpan_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:53.090291+00:00
-- url     : https://prove2.me/theorems/4493390f-b0ae-4f0d-bbcf-42e599b71b7d
-- title:
--   Harish Chandra: canon Span mono
-- statement:
--   The Harish Chandra construction uses the canon Span mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L217-L221

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

theorem GroundTheory.Automorphic.HarishChandra.canonSpan_mono {P : Fin n × Fin n → Prop} {lo lo' hi hi' : ℕ} (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : canonSpan P lo hi ≤ canonSpan P lo' hi' := by sorry
