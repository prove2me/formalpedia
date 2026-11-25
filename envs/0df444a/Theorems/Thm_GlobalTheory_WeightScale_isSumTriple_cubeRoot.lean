-- Prove2me | Theorems.Thm_GlobalTheory_WeightScale_isSumTriple_cubeRoot
-- name    : GlobalTheory.WeightScale.isSumTriple_cubeRoot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:39.376986+00:00
-- url     : https://prove2.me/theorems/71ab0472-ca2d-46e1-a05c-04fe351f378f
-- title:
--   Weight Scale: is Sum Triple cube Root
-- statement:
--   The Weight Scale construction uses the is Sum Triple cube Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsUnimodularSolTriple.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsUnimodularSolTriple.lean#L94-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsUnimodularSolTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeightScale
variable {A B : Type*} [CommRing A] [CommRing B]
open WeierstrassCurve.Projective

theorem GlobalTheory.WeightScale.isSumTriple_cubeRoot {w : A} (hw : w ^ 2 + w + 1 = 0) {X Y Z : A}
    (h : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve A).toProjective.Equation ![X, Y, Z]) :
    IsSumTriple ⟨0, 0, 1, 0, 0⟩ ![X, Y, Z] ![w * X, Y, Z] ![w ^ 2 * X, -Y - Z, Z] := by sorry
