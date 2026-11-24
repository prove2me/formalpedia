-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_constCochain
-- name    : GroundTheory.Arith.SchemeCoh.d_constCochain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:06.503017+00:00
-- url     : https://prove2.me/theorems/9a0afeef-78e5-4097-99c7-16117e7733f0
-- title:
--   Scheme Coh: d const Cochain
-- statement:
--   The Scheme Coh construction uses the d const Cochain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L43-L48

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

theorem GroundTheory.Arith.SchemeCoh.d_constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by sorry
