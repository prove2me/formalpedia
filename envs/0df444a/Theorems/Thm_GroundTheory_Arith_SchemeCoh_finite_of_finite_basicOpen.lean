-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_finite_of_finite_basicOpen
-- name    : GroundTheory.Arith.SchemeCoh.finite_of_finite_basicOpen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:52.021544+00:00
-- url     : https://prove2.me/theorems/e5027f77-877c-4ccc-8c85-c8e3ee28ed18
-- title:
--   Scheme Coh: finite of finite basic Open
-- statement:
--   The Scheme Coh construction uses the finite of finite basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/QcohLocal.lean#L277-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/QcohLocal.lean#L277-L321

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}
variable (F : X.Modules) [F.IsQuasicoherent]

theorem GroundTheory.Arith.SchemeCoh.finite_of_finite_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (s : Finset Γ(X, U))
    (hs : Ideal.span (s : Set Γ(X, U)) = ⊤)
    (h : ∀ f ∈ s, Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)) :
    Module.Finite Γ(X, U) Γ(F, U) := by sorry
