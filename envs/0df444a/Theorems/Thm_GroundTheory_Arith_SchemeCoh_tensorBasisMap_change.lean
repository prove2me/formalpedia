-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorBasisMap_change
-- name    : GroundTheory.Arith.SchemeCoh.tensorBasisMap_change
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:20.461713+00:00
-- url     : https://prove2.me/theorems/bca87745-ae84-56f9-b6b8-224a997c847d
-- title:
--   Scheme Coh: tensor Basis Map change
-- statement:
--   The Scheme Coh construction uses the tensor Basis Map change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L85-L91

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

theorem GroundTheory.Arith.SchemeCoh.tensorBasisMap_change {U' : X.Opens} (s' : ((preMod X).obj L).obj (op U')) (h : V ≤ U)
    (h' : V ≤ U') (c : ringOn X V) (hc : resM ((preMod X).obj L) h' s' = c • resM ((preMod X).obj L) h s)
    (m : Γ(M, V)) : tensorBasisMap M L s' h' m = tensorBasisMap M L s h ((show Γ(X, V) from c) • m) := by sorry
