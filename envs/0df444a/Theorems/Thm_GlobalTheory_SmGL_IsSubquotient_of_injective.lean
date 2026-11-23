-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
-- name    : GlobalTheory.SmGL.IsSubquotient.of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:39.95017+00:00
-- url     : https://prove2.me/theorems/5d19fde0-7f77-4a15-af7d-19728f886af6
-- title:
--   Is Subquotient: of injective
-- statement:
--   The Is Subquotient construction uses the of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L104-L115

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

theorem GlobalTheory.SmGL.IsSubquotient.of_injective {σ : Representation F G W} {ρ : Representation F G V}
    (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) : IsSubquotient σ ρ := by sorry
