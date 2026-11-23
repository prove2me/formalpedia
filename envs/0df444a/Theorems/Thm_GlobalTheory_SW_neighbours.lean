-- Prove2me | Theorems.Thm_GlobalTheory_SW_neighbours
-- name    : GlobalTheory.SW.neighbours
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:32.784335+00:00
-- url     : https://prove2.me/theorems/b5537d60-3630-4201-930e-f03c3a6c46da
-- title:
--   SW: neighbours
-- statement:
--   The SW construction uses the neighbours property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L457-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L457-L472

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.neighbours : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → GoodPrime M q (conjI P) ∧ conjI (conjI P) = P ∧ ∀ Λ ∈ Vset E n M, (Nb M P Λ).Finite ∧ (Nb M P Λ).ncard * (q - 1) = q ^ n - 1 ∧ (∀ Λ' ∈ Vset E n M, Λ' ∈ Nb M P Λ ↔ Λ ∈ Nb M (conjI P) Λ') ∧ (∀ Λ₀ : Lt E n, P • Λ ≤ Λ₀ → Λ₀ ≤ Λ → Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q → ∃! Λ', Λ' ∈ Nb M P Λ ∧ Λ ⊓ Λ' = Λ₀) ∧ (∀ Λ' ∈ Nb M P Λ, ∀ m : ℕ, q.Coprime m → Agree m Λ Λ') ∧ ∀ h ∈ DH E n M, ∀ Λ₁ ∈ Vset E n M, Moves h Λ Λ₁ → ∀ Λ' Λ₁' : Lt E n, Moves h Λ' Λ₁' → (Λ' ∈ Nb M P Λ ↔ Λ₁' ∈ Nb M P Λ₁) := by sorry
