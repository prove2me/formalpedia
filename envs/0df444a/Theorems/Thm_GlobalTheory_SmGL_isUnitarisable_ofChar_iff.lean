-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff
-- name    : GlobalTheory.SmGL.isUnitarisable_ofChar_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:06.425487+00:00
-- url     : https://prove2.me/theorems/d0b436ae-f023-45e7-9c01-86d5ad53dba6
-- title:
--   Sm GL: is Unitarisable of Char iff
-- statement:
--   The Sm GL construction uses the is Unitarisable of Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L311-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L311-L331

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

theorem GlobalTheory.SmGL.isUnitarisable_ofChar_iff (χ : G →* ℂˣ) : IsUnitarisable (ofChar χ) ↔ IsUnitaryChar χ := by sorry
