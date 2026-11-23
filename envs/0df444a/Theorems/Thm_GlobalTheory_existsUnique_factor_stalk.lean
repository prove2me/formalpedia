-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_factor_stalk
-- name    : GlobalTheory.existsUnique_factor_stalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:43.507316+00:00
-- url     : https://prove2.me/theorems/aed7fc92-1029-4e51-ab9f-f027f3d6eaf5
-- title:
--   Global Theory: exists Unique factor stalk
-- statement:
--   The Global Theory construction uses the exists Unique factor stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L110-L117

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
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}

theorem GlobalTheory.existsUnique_factor_stalk (f : Spec (.of R) ⟶ X) {x : X} (hx : f (closedPoint R) = x) :
    ∃! φ : X.presheaf.stalk x ⟶ .of R, Spec.map φ ≫ X.fromSpecStalk x = f := by sorry
