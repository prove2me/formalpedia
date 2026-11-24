-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_basis_det_ne_zero_of_points
-- name    : GlobalTheory.KeyKa.exists_basis_det_ne_zero_of_points
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:53.454993+00:00
-- url     : https://prove2.me/theorems/7d104b22-ea25-4e72-b84d-35085533f449
-- title:
--   Key Ka: exists basis det ne zero of points
-- statement:
--   The Key Ka construction uses the exists basis det ne zero of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrEqJacobianOfIntegralPoints.lean#L9-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrEqJacobianOfIntegralPoints.lean#L9-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.exists_basis_det_ne_zero_of_points {O B Ix : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup B] [Module O B] [Fintype Ix] [DecidableEq Ix]
    (φ : B →ₗ[O] (Ix → O)) (hφ : Function.Injective φ) (c : O) (hc : c ≠ 0)
    (hs : ∀ t : Ix → O, ∃ y, φ y = c • t) :
    ∃ b : Module.Basis Ix O B, (Matrix.of fun a a' => φ (b a') a).det ≠ 0 := by sorry
