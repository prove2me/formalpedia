-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
-- name    : GroundTheory.Arith.SchemeCoh.d_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:11.071805+00:00
-- url     : https://prove2.me/theorems/5136053f-ef9a-4fc1-9782-3066072de4dd
-- title:
--   Scheme Coh: d apply
-- statement:
--   The Scheme Coh construction uses the d apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L67-L74

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.d_apply (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 2) → ι) :
    d P U n σ i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      res P (inter_le_comp U i k.succAbove) (σ (i ∘ k.succAbove)) := by sorry
