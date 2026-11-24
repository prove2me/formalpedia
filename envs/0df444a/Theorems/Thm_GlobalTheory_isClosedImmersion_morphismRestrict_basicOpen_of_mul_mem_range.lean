-- Prove2me | Theorems.Thm_GlobalTheory_isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range
-- name    : GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:42.315605+00:00
-- url     : https://prove2.me/theorems/0937ed98-85db-44cd-b2e4-9bcd69cdd76a
-- title:
--   Global Theory: is Closed Immersion morphism Restrict basic Open of mul mem range
-- statement:
--   The Global Theory construction uses the is Closed Immersion morphism Restrict basic Open of mul mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulM.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedImmersionMorphismRestrictBasicOpenOfMulM.lean#L45-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulM
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
open GlobalTheory

theorem GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by sorry
