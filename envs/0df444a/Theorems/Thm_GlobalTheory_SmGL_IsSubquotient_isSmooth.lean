-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_isSmooth
-- name    : GlobalTheory.SmGL.IsSubquotient.isSmooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:33.615593+00:00
-- url     : https://prove2.me/theorems/d3fd9e86-c5de-4286-833d-4dbd13ca9bfc
-- title:
--   Is Subquotient: is Smooth
-- statement:
--   The Is Subquotient construction uses the is Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L226-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L226-L235

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

theorem GlobalTheory.SmGL.IsSubquotient.isSmooth {σ : Representation F G W} {ρ : Representation F G V}
    (h : IsSubquotient σ ρ) (hρ : IsSmooth ρ) : IsSmooth σ := by sorry
