-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_restr_add
-- name    : GroundTheory.Arith.SchemeCoh.DualSec.restr_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:45.629359+00:00
-- url     : https://prove2.me/theorems/5e182c8d-2264-40b7-bc00-ed8fbbcf9078
-- title:
--   Dual Sec: restr add
-- statement:
--   The Dual Sec construction uses the restr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L112-L113

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
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
open GroundTheory.Arith.SchemeCoh.DualSec
variable {P : PMod X}

theorem GroundTheory.Arith.SchemeCoh.DualSec.restr_add {U U' : X.Opens} (hU : U' ≤ U) (φ ψ : DualSec P U) :
    restr hU (φ + ψ) = restr hU φ + restr hU ψ := by sorry
