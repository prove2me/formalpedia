-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_mem_wordSpan
-- name    : GroundTheory.Automorphic.HarishChandra.e_mul_mem_wordSpan
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:53.031451+00:00
-- url     : https://prove2.me/theorems/35512033-ce9d-4086-bbfe-0cd48ed88261
-- title:
--   Harish Chandra: e mul mem word Span
-- statement:
--   The Harish Chandra construction uses the e mul mem word Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L36-L49

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

theorem GroundTheory.Automorphic.HarishChandra.e_mul_mem_wordSpan {P : Fin n × Fin n → Prop} {a : Fin n × Fin n} (ha : P a) {k : ℕ}
    {u : U n} (hu : u ∈ wordSpan P k) : e a * u ∈ wordSpan P (k + 1) := by sorry
