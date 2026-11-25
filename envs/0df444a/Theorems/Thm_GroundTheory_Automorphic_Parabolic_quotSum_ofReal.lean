-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotSum_ofReal
-- name    : GroundTheory.Automorphic.Parabolic.quotSum_ofReal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:39.453073+00:00
-- url     : https://prove2.me/theorems/b7ce9016-f63c-5c5a-8076-6379dc674af6
-- title:
--   Parabolic: quot Sum of Real
-- statement:
--   The Parabolic construction uses the quot Sum of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L210-L214

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
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
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

theorem GroundTheory.Automorphic.Parabolic.quotSum_ofReal {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out) :
    quotSum H (fun g => (Φ g : ℂ)) = ((quotSum H Φ : ℝ) : ℂ) := by sorry
