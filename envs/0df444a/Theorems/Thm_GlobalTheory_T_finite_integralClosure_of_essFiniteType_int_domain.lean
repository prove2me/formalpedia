-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_integralClosure_of_essFiniteType_int_domain
-- name    : GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:40.872382+00:00
-- url     : https://prove2.me/theorems/5e88d99c-b9fc-4702-9751-c2cc5f4f2e86
-- title:
--   T: finite integral Closure of ess Finite Type int domain
-- statement:
--   The T construction uses the finite integral Closure of ess Finite Type int domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by sorry
