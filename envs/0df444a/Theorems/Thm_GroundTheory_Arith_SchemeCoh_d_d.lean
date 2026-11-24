-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_d
-- name    : GroundTheory.Arith.SchemeCoh.d_d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:16.159897+00:00
-- url     : https://prove2.me/theorems/f5f05733-e1a5-4d85-a037-cbe7366f78d6
-- title:
--   Scheme Coh: d d
-- statement:
--   The Scheme Coh construction uses the d d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L76-L79

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

theorem GroundTheory.Arith.SchemeCoh.d_d (n : ℕ) (σ : Cochain P U n) : d P U (n + 1) (d P U n σ) = 0 := by sorry
