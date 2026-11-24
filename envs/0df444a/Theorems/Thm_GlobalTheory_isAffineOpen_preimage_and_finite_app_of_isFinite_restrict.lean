-- Prove2me | Theorems.Thm_GlobalTheory_isAffineOpen_preimage_and_finite_app_of_isFinite_restrict
-- name    : GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:21.903958+00:00
-- url     : https://prove2.me/theorems/8b8ca141-366d-43da-841b-5b7624f56be1
-- title:
--   Global Theory: is Affine Open preimage and finite app of is Finite restrict
-- statement:
--   The Global Theory construction uses the is Affine Open preimage and finite app of is Finite restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
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

theorem GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by sorry
