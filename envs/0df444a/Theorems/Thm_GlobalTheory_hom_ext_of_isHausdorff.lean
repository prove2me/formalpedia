-- Prove2me | Theorems.Thm_GlobalTheory_hom_ext_of_isHausdorff
-- name    : GlobalTheory.hom_ext_of_isHausdorff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:15.00152+00:00
-- url     : https://prove2.me/theorems/83624e1c-b7bd-4fae-ba70-f508d0532c03
-- title:
--   Global Theory: hom ext of is Hausdorff
-- statement:
--   The Global Theory construction uses the hom ext of is Hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L272-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L272-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.hom_ext_of_isHausdorff (I : Ideal R) [IsHausdorff I R] {X : Scheme.{u}}
    {g g' : Spec (.of R) ⟶ X}
    (h : ∀ n, adicLevelι I (n + 1) ≫ g = adicLevelι I (n + 1) ≫ g') : g = g' := by sorry
