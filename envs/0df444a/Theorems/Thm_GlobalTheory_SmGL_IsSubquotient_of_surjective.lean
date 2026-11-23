-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_surjective
-- name    : GlobalTheory.SmGL.IsSubquotient.of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:00.952466+00:00
-- url     : https://prove2.me/theorems/85545d79-c41a-40e4-8583-bce02109a8a2
-- title:
--   Is Subquotient: of surjective
-- statement:
--   The Is Subquotient construction uses the of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L63-L69

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

theorem GlobalTheory.SmGL.IsSubquotient.of_surjective {σ : Representation F G W} {ρ : Representation F G V}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSubquotient σ ρ := by sorry
