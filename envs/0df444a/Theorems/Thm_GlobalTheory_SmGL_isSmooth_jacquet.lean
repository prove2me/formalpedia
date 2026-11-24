-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_isSmooth_jacquet
-- name    : GlobalTheory.SmGL.isSmooth_jacquet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:03.887795+00:00
-- url     : https://prove2.me/theorems/c9b7fbb4-79c2-423b-b53c-636d0b441fc7
-- title:
--   Sm GL: is Smooth jacquet
-- statement:
--   The Sm GL construction uses the is Smooth jacquet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L242-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L242-L251

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

theorem GlobalTheory.SmGL.isSmooth_jacquet [TopologicalSpace H] [IsTopologicalGroup H] {ρ : Representation F G V}
    (hρ : IsSmooth ρ) (N : Subgroup G) (s : H →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (hc : Continuous s) :
    IsSmooth (jacquet ρ N s hs) := by sorry
