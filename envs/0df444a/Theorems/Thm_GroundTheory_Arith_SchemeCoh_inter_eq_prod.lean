-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_eq_prod
-- name    : GroundTheory.Arith.SchemeCoh.inter_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:10.102543+00:00
-- url     : https://prove2.me/theorems/ce977531-8309-4e4e-9079-2961f2fd61c9
-- title:
--   Scheme Coh: inter eq prod
-- statement:
--   The Scheme Coh construction uses the inter eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean#L95-L105

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
variable (h : ι → R)
include A

theorem GroundTheory.Arith.SchemeCoh.inter_eq_prod : ∀ {m : ℕ} (I : Fin (m + 1) → ι), inter (D ∘ h) I = D (∏ a, h (I a))
  := by sorry
