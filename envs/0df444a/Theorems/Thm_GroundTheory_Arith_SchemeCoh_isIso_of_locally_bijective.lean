-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_of_locally_bijective
-- name    : GroundTheory.Arith.SchemeCoh.isIso_of_locally_bijective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:12.784511+00:00
-- url     : https://prove2.me/theorems/278334d6-5c1b-41ce-bcef-1d9b31765db5
-- title:
--   Scheme Coh: is Iso of locally bijective
-- statement:
--   The Scheme Coh construction uses the is Iso of locally bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L285-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L285-L325

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

theorem GroundTheory.Arith.SchemeCoh.isIso_of_locally_bijective {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (f.app V)) : IsIso f := by sorry
