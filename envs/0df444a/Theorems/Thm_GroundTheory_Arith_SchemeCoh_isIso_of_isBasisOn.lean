-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_of_isBasisOn
-- name    : GroundTheory.Arith.SchemeCoh.isIso_of_isBasisOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:44.095599+00:00
-- url     : https://prove2.me/theorems/d7dd5243-d54e-4d71-a187-1f79ec5d4d0b
-- title:
--   Scheme Coh: is Iso of is Basis On
-- statement:
--   The Scheme Coh construction uses the is Iso of is Basis On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L340-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L340-L347

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

theorem GroundTheory.Arith.SchemeCoh.isIso_of_isBasisOn {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
      IsBasisOn ((preMod X).obj M) U s ∧ IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) :
    IsIso f := by sorry
