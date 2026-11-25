-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_wordSpan
-- name    : GroundTheory.Automorphic.HarishChandra.mul_mem_wordSpan
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:05.605787+00:00
-- url     : https://prove2.me/theorems/6872d850-6cbe-511d-80de-69a4f1aa8ec3
-- title:
--   Harish Chandra: mul mem word Span
-- statement:
--   The Harish Chandra construction uses the mul mem word Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L51-L59

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

theorem GroundTheory.Automorphic.HarishChandra.mul_mem_wordSpan {P : Fin n × Fin n → Prop} {v : List (Fin n × Fin n)}
    (hv : ∀ a ∈ v, P a) {k : ℕ} {u : U n} (hu : u ∈ wordSpan P k) :
    word v * u ∈ wordSpan P (v.length + k) := by sorry
