-- Prove2me | Theorems.Thm_GlobalTheory_SW_NearPrim_integral_coord
-- name    : GlobalTheory.SW.NearPrim.integral_coord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:41.647277+00:00
-- url     : https://prove2.me/theorems/40b90e53-48c8-4966-8aab-bad91761308d
-- title:
--   Near Prim: integral coord
-- statement:
--   The Near Prim construction uses the integral coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L120-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsNearlyPrimitive.lean#L120-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim

theorem GlobalTheory.SW.NearPrim.integral_coord {E : Type} [Field E] [NumberField E] {k : ℕ}
    (L : AddSubgroup (Fin k → E))
    (hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L) (M : ℕ)
    (hM : ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1)
    (a : Matrix (Fin k) (Fin k) E) (haL : ∀ i, a i ∈ L) (ha0 : ∀ i j, i < j → a i j = 0)
    (hai : ∀ i, a i i ≠ 0)
    (hmin : ∀ i, ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i i)‖ ≤ ‖canonicalEmbedding E (s i)‖) (p : ℕ) (hp : p ≤ k) :
    ∀ t : Fin k → E, (∀ j : Fin k, p ≤ j → t j = 0) → t ᵥ* a ∈ L →
      ∀ i, IsIntegral ℤ (((M.factorial ^ p : ℕ) : E) * t i) := by sorry
