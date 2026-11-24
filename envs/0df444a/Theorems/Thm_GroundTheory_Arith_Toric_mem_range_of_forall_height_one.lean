-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_mem_range_of_forall_height_one
-- name    : GroundTheory.Arith.Toric.mem_range_of_forall_height_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:15.309454+00:00
-- url     : https://prove2.me/theorems/8a8500d8-df06-420c-86b9-5a82e398dbb5
-- title:
--   Toric: mem range of forall height one
-- statement:
--   The Toric construction uses the mem range of forall height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L73-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L73-L95

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem GroundTheory.Arith.Toric.mem_range_of_forall_height_one {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K) (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ a s : A, s ∉ p ∧ x * algebraMap A K s = algebraMap A K a) :
    x ∈ (algebraMap A K).range := by sorry
