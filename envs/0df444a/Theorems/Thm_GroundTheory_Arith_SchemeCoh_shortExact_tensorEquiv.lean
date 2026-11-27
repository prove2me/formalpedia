-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_shortExact_tensorEquiv
-- name    : GroundTheory.Arith.SchemeCoh.shortExact_tensorEquiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:00:42.867662+00:00
-- url     : https://prove2.me/theorems/c071251b-736b-59bd-90f3-85808c475d8e
-- title:
--   Scheme Coh: short Exact tensor Equiv
-- statement:
--   The Scheme Coh construction uses the short Exact tensor Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean#L192-L194

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

theorem GroundTheory.Arith.SchemeCoh.shortExact_tensorEquiv (hL : IsInvertibleSheaf L) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (tensorEquivOfInvertible hL).functor).ShortExact := by sorry
