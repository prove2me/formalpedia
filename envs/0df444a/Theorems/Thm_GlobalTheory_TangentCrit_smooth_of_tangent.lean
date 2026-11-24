-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_smooth_of_tangent
-- name    : GlobalTheory.TangentCrit.smooth_of_tangent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:05.724532+00:00
-- url     : https://prove2.me/theorems/e241140a-5b60-49b0-9fa8-f2568a31c7b6
-- title:
--   Tangent Crit: smooth of tangent
-- statement:
--   The Tangent Crit construction uses the smooth of tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L238-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L238-L284

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u

theorem GlobalTheory.TangentCrit.smooth_of_tangent {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) [Smooth (f ≫ π)]
    [LocallyOfFiniteType π]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
      (v : Spec (.of (DualNumber k)) ⟶ Y), dualPt k ≫ v = x ≫ f → v ≫ π = dualBase k ≫ x ≫ f ≫ π →
      ∃ w : Spec (.of (DualNumber k)) ⟶ X, dualPt k ≫ w = x ∧ w ≫ f = v) :
    Smooth f := by sorry
