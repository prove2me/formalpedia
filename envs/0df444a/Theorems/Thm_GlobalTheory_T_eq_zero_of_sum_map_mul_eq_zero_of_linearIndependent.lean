-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent
-- name    : GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:49.32531+00:00
-- url     : https://prove2.me/theorems/2a854fbd-ecc7-4b98-89be-2270459b9780
-- title:
--   T: eq zero of sum map mul eq zero of linear Independent
-- statement:
--   The T construction uses the eq zero of sum map mul eq zero of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisLinearDisjointStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisLinearDisjointStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by sorry
