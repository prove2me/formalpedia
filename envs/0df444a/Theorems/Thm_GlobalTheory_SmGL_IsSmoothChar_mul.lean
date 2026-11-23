-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
-- name    : GlobalTheory.SmGL.IsSmoothChar.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:34.556626+00:00
-- url     : https://prove2.me/theorems/f16f4978-ae6a-479e-a32b-5f33d085930a
-- title:
--   Is Smooth Char: mul
-- statement:
--   The Is Smooth Char construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L208-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem GlobalTheory.SmGL.IsSmoothChar.mul {χ ψ : G →* Fˣ} (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) :
    IsSmoothChar (χ * ψ) := by sorry
