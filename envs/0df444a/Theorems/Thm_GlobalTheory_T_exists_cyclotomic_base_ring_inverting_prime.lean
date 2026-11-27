-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cyclotomic_base_ring_inverting_prime
-- name    : GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:46.429655+00:00
-- url     : https://prove2.me/theorems/8cfd2311-9b04-5be8-9c24-5daa4d1eabc8
-- title:
--   T: exists cyclotomic base ring inverting prime
-- statement:
--   The T construction uses the exists cyclotomic base ring inverting prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCyclotomicBaseRingInvertingPrimeStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCyclotomicBaseRingInvertingPrimeStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e → k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (j : o →+* ZP p k), ArBase em ∧ j (b.ζ : o) = zetaZP p k ∧ (∀ x, ((j x : ZP p k) : ℂ) = em x) ∧ ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y := by sorry
