-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_range_of_isPullback
-- name    : GlobalTheory.FinEt.range_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:32.039201+00:00
-- url     : https://prove2.me/theorems/e4c31709-33f3-4a93-bb43-bc30f671489b
-- title:
--   Fin Et: range of is Pullback
-- statement:
--   The Fin Et construction uses the range of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

theorem GlobalTheory.FinEt.range_of_isPullback {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by sorry
