-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
-- name    : GlobalTheory.SmGL.IsSmoothChar.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:01.997216+00:00
-- url     : https://prove2.me/theorems/97171d48-92da-4465-8dd9-06247d6f89e7
-- title:
--   Is Smooth Char: comp
-- statement:
--   The Is Smooth Char construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L179-L181

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

theorem GlobalTheory.SmGL.IsSmoothChar.comp [TopologicalSpace H] {χ : G →* Fˣ} (hχ : IsSmoothChar χ) (s : H →* G)
    (hs : Continuous s) : IsSmoothChar (χ.comp s) := by sorry
