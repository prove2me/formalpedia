-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bijective_mulSection_app
-- name    : GroundTheory.Arith.SchemeCoh.bijective_mulSection_app
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:49.876808+00:00
-- url     : https://prove2.me/theorems/8637cbd2-443d-4905-b4eb-732d734f54ed
-- title:
--   Scheme Coh: bijective mul Section app
-- statement:
--   The Scheme Coh construction uses the bijective mul Section app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L117-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L117-L137

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}
variable (M L : X.Modules) (s : Γ(L, ⊤))

theorem GroundTheory.Arith.SchemeCoh.bijective_mulSection_app {W : X.Opens}
    (hs : IsBasisOn ((preMod X).obj L) W (resM ((preMod X).obj L) le_top s)) :
    ∀ V ≤ W, Function.Bijective ((mulSection M L s).app V) := by sorry
