-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_finite_basicOpen
-- name    : GroundTheory.Arith.SchemeCoh.finite_basicOpen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:26.3988+00:00
-- url     : https://prove2.me/theorems/a5ff1f71-5855-5307-b428-a6ea1cfa27bf
-- title:
--   Scheme Coh: finite basic Open
-- statement:
--   The Scheme Coh construction uses the finite basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/QcohLocal.lean#L225-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/QcohLocal.lean#L225-L244

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

theorem GroundTheory.Arith.SchemeCoh.finite_basicOpen {V : X.Opens} (hV : IsAffineOpen V) [Module.Finite Γ(X, V) Γ(F, V)]
    (g : Γ(X, V)) : Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) := by sorry
