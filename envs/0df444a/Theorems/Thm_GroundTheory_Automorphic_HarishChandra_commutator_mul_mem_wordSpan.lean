-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_commutator_mul_mem_wordSpan
-- name    : GroundTheory.Automorphic.HarishChandra.commutator_mul_mem_wordSpan
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:52.42873+00:00
-- url     : https://prove2.me/theorems/c691a9d9-e12c-4b98-a2ac-ace337e8b11b
-- title:
--   Harish Chandra: commutator mul mem word Span
-- statement:
--   The Harish Chandra construction uses the commutator mul mem word Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L61-L81

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

theorem GroundTheory.Automorphic.HarishChandra.commutator_mul_mem_wordSpan {P : Fin n × Fin n → Prop} (hP : Closed P)
    {a b : Fin n × Fin n} (ha : P a) (hb : P b) {l : List (Fin n × Fin n)} (hl : ∀ c ∈ l, P c) :
    (e a * e b - e b * e a) * word l ∈ wordSpan P (l.length + 1) := by sorry
