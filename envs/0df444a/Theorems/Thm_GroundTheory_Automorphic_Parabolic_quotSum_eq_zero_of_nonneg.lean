-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotSum_eq_zero_of_nonneg
-- name    : GroundTheory.Automorphic.Parabolic.quotSum_eq_zero_of_nonneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:08.080841+00:00
-- url     : https://prove2.me/theorems/0ca1ca35-bd73-47b0-bb23-5b8fb14307e9
-- title:
--   Parabolic: quot Sum eq zero of nonneg
-- statement:
--   The Parabolic construction uses the quot Sum eq zero of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean#L14-L22

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

theorem GroundTheory.Automorphic.Parabolic.quotSum_eq_zero_of_nonneg {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hΦ : ∀ g, 0 ≤ Φ g) (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out)
    (h0 : quotSum H Φ = 0) (q : G ⧸ H) : Φ q.out = 0 := by sorry
