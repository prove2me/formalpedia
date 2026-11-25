-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_finite_support_quotSum
-- name    : GroundTheory.Automorphic.Parabolic.finite_support_quotSum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:18.490984+00:00
-- url     : https://prove2.me/theorems/4424e0ab-d30a-4079-87fa-8887edbf9f90
-- title:
--   Parabolic: finite support quot Sum
-- statement:
--   The Parabolic construction uses the finite support quot Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L49-L62

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
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
open Function
open scoped Pointwise
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
variable {H}
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.Parabolic.finite_support_quotSum (hH : IsOpen (H : Set G)) (hZH : Subgroup.center G ≤ H)
    {Φ : G → M} {C : Set G} (hC : IsCompact C)
    (hsupp : support Φ ⊆ (Subgroup.center G : Set G) * C) :
    (support fun q : G ⧸ H => Φ q.out).Finite := by sorry
