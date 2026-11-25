-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_sum_quotient_out_of_le
-- name    : GroundTheory.Automorphic.Parabolic.sum_quotient_out_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:52.794799+00:00
-- url     : https://prove2.me/theorems/cc90b19d-3c6f-4326-8a6a-a7bd6c790239
-- title:
--   Parabolic: sum quotient out of le
-- statement:
--   The Parabolic construction uses the sum quotient out of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L16-L31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {α : Type*} [Group α] {W : Type*} [AddCommGroup W]

theorem GroundTheory.Automorphic.Parabolic.sum_quotient_out_of_le {s t : Subgroup α} (h : s ≤ t) [Fintype (α ⧸ s)] [Fintype (α ⧸ t)]
    [Fintype (t ⧸ s.subgroupOf t)] (φ : α → W) (hφ : ∀ a, ∀ b ∈ t, φ (a * b) = φ a) :
    ∑ q : α ⧸ s, φ (Quotient.out q) = (s.relIndex t) • ∑ q : α ⧸ t, φ (Quotient.out q) := by sorry
