-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_zero_apply
-- name    : GroundTheory.Arith.SchemeCoh.d_zero_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:36.072668+00:00
-- url     : https://prove2.me/theorems/98cdef94-9986-4a48-8057-bbbf5c970248
-- title:
--   Scheme Coh: d zero apply
-- statement:
--   The Scheme Coh construction uses the d zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L34-L38

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

theorem GroundTheory.Arith.SchemeCoh.d_zero_apply (σ : Cochain P U 0) (i : Fin 2 → ι) :
    d P U 0 σ i = res P (inter_le_comp U i (0 : Fin 2).succAbove) (σ (i ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U i (1 : Fin 2).succAbove) (σ (i ∘ (1 : Fin 2).succAbove)) := by sorry
