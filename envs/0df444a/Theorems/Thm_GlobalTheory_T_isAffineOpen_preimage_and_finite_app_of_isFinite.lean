-- Prove2me | Theorems.Thm_GlobalTheory_T_isAffineOpen_preimage_and_finite_app_of_isFinite
-- name    : GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:25.676806+00:00
-- url     : https://prove2.me/theorems/1c937e1e-2770-5ef0-bf65-10d294645ad2
-- title:
--   T: is Affine Open preimage and finite app of is Finite
-- statement:
--   The T construction uses the is Affine Open preimage and finite app of is Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestriStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestriStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestriStatement
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

theorem GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) → IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by sorry
