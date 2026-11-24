-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_map_mul_right_eq_of_finite_fundamentalDomain
-- name    : GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:02.565869+00:00
-- url     : https://prove2.me/theorems/d16fe4ed-0ef9-4992-931b-a6428d9beff4
-- title:
--   T: haar map mul right eq of finite fundamental Domain
-- statement:
--   The T construction uses the haar map mul right eq of finite fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapMulRightEqOfFiniteFundamentalDomainStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMapMulRightEqOfFiniteFundamentalDomainStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightEqOfFiniteFundamentalDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightEqOfFiniteFundamentalDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by sorry
