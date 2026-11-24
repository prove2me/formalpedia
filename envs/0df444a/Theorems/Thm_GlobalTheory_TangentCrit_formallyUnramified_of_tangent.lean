-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_formallyUnramified_of_tangent
-- name    : GlobalTheory.TangentCrit.formallyUnramified_of_tangent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:16.673704+00:00
-- url     : https://prove2.me/theorems/7cfcb511-0edf-4488-884a-eadb5e1407e9
-- title:
--   Tangent Crit: formally Unramified of tangent
-- statement:
--   The Tangent Crit construction uses the formally Unramified of tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L166-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L166-L180

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

theorem GlobalTheory.TangentCrit.formallyUnramified_of_tangent {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (w : Spec (.of (DualNumber k)) ⟶ X),
      w ≫ f = dualBase k ≫ dualPt k ≫ w ≫ f → w = dualBase k ≫ dualPt k ≫ w) :
    FormallyUnramified f := by sorry
