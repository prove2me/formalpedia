-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorBasisMap_res
-- name    : GroundTheory.Arith.SchemeCoh.tensorBasisMap_res
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:04:03.667801+00:00
-- url     : https://prove2.me/theorems/513b9c01-7d65-55a7-aa72-d0f72d59a875
-- title:
--   Scheme Coh: tensor Basis Map res
-- statement:
--   The Scheme Coh construction uses the tensor Basis Map res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L72-L83

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

theorem GroundTheory.Arith.SchemeCoh.tensorBasisMap_res (h : V ≤ U) {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V)) :
    resF (M ⊗ L) hWV (tensorBasisMap M L s h m) =
      tensorBasisMap M L s (hWV.trans h) (resF M hWV m) := by sorry
