-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_of_isFaceOf
-- name    : GroundTheory.Arith.Toric.IsRationalPolyhedral.of_isFaceOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:03.703259+00:00
-- url     : https://prove2.me/theorems/4a14c9c4-f735-467a-afc2-9a785a3b29e8
-- title:
--   Is Rational Polyhedral: of is Face Of
-- statement:
--   The Is Rational Polyhedral construction uses the of is Face Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/ToricFaces.lean#L9-L27

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct

theorem GroundTheory.Arith.Toric.IsRationalPolyhedral.of_isFaceOf {L E : Type*} [AddCommGroup L] [AddCommGroup E]
    [Module ℝ E] {ι : L →ₗ[ℤ] E} {σ τ : PointedCone ℝ E} (hσ : IsRationalPolyhedral ι σ)
    (hτ : τ.IsFaceOf σ) : IsRationalPolyhedral ι τ := by sorry
