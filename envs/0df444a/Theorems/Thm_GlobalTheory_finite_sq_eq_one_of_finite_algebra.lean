-- Prove2me | Theorems.Thm_GlobalTheory_finite_sq_eq_one_of_finite_algebra
-- name    : GlobalTheory.finite_sq_eq_one_of_finite_algebra
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:02.094747+00:00
-- url     : https://prove2.me/theorems/d9431214-5228-4f51-a353-73e76455f5c3
-- title:
--   Global Theory: finite sq eq one of finite algebra
-- statement:
--   The Global Theory construction uses the finite sq eq one of finite algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSqEqOneOfFiniteAlgebra.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSqEqOneOfFiniteAlgebra.lean#L5-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finite_sq_eq_one_of_finite_algebra (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by sorry
