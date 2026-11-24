-- Prove2me | Theorems.Thm_GlobalTheory_prod_classGroup_mk0_eq_of_pi_linearEquiv
-- name    : GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:47.010269+00:00
-- url     : https://prove2.me/theorems/2a6b70fe-208b-41d3-8ab6-6f4300e1c1b2
-- title:
--   Global Theory: prod class Group mk0 eq of pi linear Equiv
-- statement:
--   The Global Theory construction uses the prod class Group mk0 eq of pi linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L126-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L126-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory.DetClass

theorem GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv (R : Type) [CommRing R] [IsDedekindDomain R]
    (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰)
    (h : Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R)))) :
    ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by sorry
