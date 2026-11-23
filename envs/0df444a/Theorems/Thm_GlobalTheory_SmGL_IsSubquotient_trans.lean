-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- name    : GlobalTheory.SmGL.IsSubquotient.trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:00.42633+00:00
-- url     : https://prove2.me/theorems/cbc2949d-2452-4252-bc28-780970b6eba0
-- title:
--   Is Subquotient: trans
-- statement:
--   The Is Subquotient construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L74-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L74-L102

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

theorem GlobalTheory.SmGL.IsSubquotient.trans {τ : Representation F G U} {σ : Representation F G W}
    {ρ : Representation F G V} (h₁ : IsSubquotient τ σ) (h₂ : IsSubquotient σ ρ) :
    IsSubquotient τ ρ := by sorry
