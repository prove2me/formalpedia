-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_IsFine_mono
-- name    : GroundTheory.Automorphic.MeasurablePartition.IsFine.mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:04.955551+00:00
-- url     : https://prove2.me/theorems/553ddbe1-aef9-4045-9dfa-592275a93f30
-- title:
--   Is Fine: mono
-- statement:
--   The Is Fine construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L70-L71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
open GroundTheory.Automorphic.MeasurablePartition
variable {X : Type*} [MeasurableSpace X]
variable (p : MeasurablePartition X)
variable {p}

theorem GroundTheory.Automorphic.MeasurablePartition.IsFine.mono {V W : SetRel X X} (h : p.IsFine V) (hVW : V ⊆ W) : p.IsFine W := by sorry
