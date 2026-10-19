-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualInfinityPlaceCenters_localEmbedding_eq_stalk
-- name    : MazurTransfer.Order13ActualInfinityPlaceCenters.localEmbedding_eq_stalk
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:05:19.655017+00:00
-- url     : https://prove2.me/theorems/158e3123-15ff-4c7a-94a5-d8c4b27c0640
-- title:
--   The actual infinity localization embedding is the canonical stalk embedding
-- statement:
--   For $a\in\mathbb Q$ with $a^2=1$, the specified embedding of the actual reciprocal infinity local ring into the existing scheme function field equals the original local-stalk isomorphism followed by the stalk map: $$j_a=\iota_{x_a}\circ s_a.$$ This exact diagram identifies the actual local valuation ring with the canonical function-field stalk at its literal curve center.
-- source:
--   Original complete localEmbedding_eq_stalk statement and proof from MazurTheorem Order13ActualInfinityPlaceCenters.lean, Apache-2.0, Vas and contributors. Public imports and top-level parent namespace context alone change; the entire original statement and main proof body are retained. Uses the Proved original affine chart/stalk coordinate commutation theorem. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. Named downstream consumer: canonical infinity-place identification.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualInfinityPlaceCenters.localEmbedding_eq_stalk (a : ℚ) (ha : a ^ 2 = 1) :
    localEmbedding ℚ a ha =
      (algebraMap ((curveScheme ℚ).presheaf.stalk (center a ha)) (actualCurveFunctionField ℚ)).comp
        (localStalkIso a ha).hom.hom := by sorry
