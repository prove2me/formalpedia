-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorBasisMap_apply
-- name    : GroundTheory.Arith.SchemeCoh.tensorBasisMap_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:58:57.812507+00:00
-- url     : https://prove2.me/theorems/7488ef80-4668-5ae3-9847-3586168154d1
-- title:
--   Scheme Coh: tensor Basis Map apply
-- statement:
--   The Scheme Coh construction uses the tensor Basis Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L35-L38

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}

theorem GroundTheory.Arith.SchemeCoh.tensorBasisMap_apply (h : V ≤ U) (m : Γ(M, V)) :
    tensorBasisMap M L s h m = (tensorToSheaf M L).app (op V)
      ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
        ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) := by sorry
