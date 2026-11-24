-- Prove2me | Theorems.Thm_GlobalTheory_Phase_VacShape_shape_at
-- name    : GlobalTheory.Phase.VacShape.shape_at
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:35.092202+00:00
-- url     : https://prove2.me/theorems/6e42a11c-99bb-4f1d-ac75-0bfaaba1e1c0
-- title:
--   Vac Shape: shape at
-- statement:
--   The Vac Shape construction uses the shape at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L60-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L60-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}

theorem GlobalTheory.Phase.VacShape.shape_at (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) :
    ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧
      ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0) := by sorry
