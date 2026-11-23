-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
-- name    : GlobalTheory.SmGL.isSmooth_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:59.355564+00:00
-- url     : https://prove2.me/theorems/dd8dd560-45ed-4626-9cf1-d9ff36182dd8
-- title:
--   Sm GL: is Smooth comp
-- statement:
--   The Sm GL construction uses the is Smooth comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L175-L177

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

theorem GlobalTheory.SmGL.isSmooth_comp [TopologicalSpace H] {ρ : Representation F G V} (hρ : IsSmooth ρ) (s : H →* G)
    (hs : Continuous s) : IsSmooth (ρ.comp s : Representation F H V) := by sorry
