-- Prove2me | Theorems.Thm_GlobalTheory_T_isClosedImmersion_restrict_basicOpen_of_mul_mem_range
-- name    : GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:35.125848+00:00
-- url     : https://prove2.me/theorems/5387f633-ff51-4510-9c5f-94b9abb63137
-- title:
--   T: is Closed Immersion restrict basic Open of mul mem range
-- statement:
--   The T construction uses the is Closed Immersion restrict basic Open of mul mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulM
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) → ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) → IsClosedImmersion (φ ∣_ Z.basicOpen r) := by sorry
