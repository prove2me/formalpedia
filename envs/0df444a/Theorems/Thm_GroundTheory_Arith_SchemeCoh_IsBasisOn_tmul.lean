-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_tmul
-- name    : GroundTheory.Arith.SchemeCoh.IsBasisOn.tmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:26.629557+00:00
-- url     : https://prove2.me/theorems/03bc9e42-d45d-48e4-ae3d-7627a304d417
-- title:
--   Is Basis On: tmul
-- statement:
--   The Is Basis On construction uses the tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L237-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L237-L257

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

theorem GroundTheory.Arith.SchemeCoh.IsBasisOn.tmul {P Q : PMod X} {U : X.Opens} {s : P.obj (op U)} {t : Q.obj (op U)}
    (hs : IsBasisOn P U s) (ht : IsBasisOn Q U t) :
    IsBasisOn (P ⊗ Q) U (s ⊗ₜ t : (P ⊗ Q).obj (op U)) := by sorry
