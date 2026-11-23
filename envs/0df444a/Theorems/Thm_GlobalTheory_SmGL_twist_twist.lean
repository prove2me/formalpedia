-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_twist_twist
-- name    : GlobalTheory.SmGL.twist_twist
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:10.427628+00:00
-- url     : https://prove2.me/theorems/3658c8b0-a73a-4c27-a3ff-322c6924580d
-- title:
--   Sm GL: twist twist
-- statement:
--   The Sm GL construction uses the twist twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L27-L29

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

theorem GlobalTheory.SmGL.twist_twist (ρ : Representation F G V) (χ ψ : G →* Fˣ) :
    twist (twist ρ χ) ψ = twist ρ (ψ * χ) := by sorry
