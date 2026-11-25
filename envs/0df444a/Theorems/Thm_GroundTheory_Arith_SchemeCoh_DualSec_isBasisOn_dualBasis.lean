-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_isBasisOn_dualBasis
-- name    : GroundTheory.Arith.SchemeCoh.DualSec.isBasisOn_dualBasis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:52.690251+00:00
-- url     : https://prove2.me/theorems/a9a8182b-5a08-4641-b782-b932c32b064c
-- title:
--   Dual Sec: is Basis On dual Basis
-- statement:
--   The Dual Sec construction uses the is Basis On dual Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L299-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L299-L322

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
variable {P : PMod X} {U : X.Opens} {s : P.obj (op U)}

theorem GroundTheory.Arith.SchemeCoh.DualSec.isBasisOn_dualBasis (hs : IsBasisOn P U s) : IsBasisOn (dualPre P) U (dualBasis hs) := by sorry
