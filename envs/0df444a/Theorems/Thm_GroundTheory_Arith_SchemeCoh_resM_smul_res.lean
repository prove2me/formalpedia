-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul_res
-- name    : GroundTheory.Arith.SchemeCoh.resM_smul_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:21.088006+00:00
-- url     : https://prove2.me/theorems/34731c3f-2654-4334-91a5-f9d0983713de
-- title:
--   Scheme Coh: res M smul res
-- statement:
--   The Scheme Coh construction uses the res M smul res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L131-L133

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.resM_smul_res (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X V)
    (x : P.obj (op U)) : resM P i (r • resM P h x) = resR i r • resM P (i.trans h) x := by sorry
