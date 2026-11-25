-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_overEquivalence_inverse_left
-- name    : GroundTheory.Arith.SchemeCoh.overEquivalence_inverse_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:34.983216+00:00
-- url     : https://prove2.me/theorems/429efcae-5ba5-5689-854d-200629cff8b9
-- title:
--   Scheme Coh: over Equivalence inverse left
-- statement:
--   The Scheme Coh construction uses the over Equivalence inverse left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SheafHEquiv.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SheafHEquiv.lean#L65-L72

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafHOver
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SheafHEquiv
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
open CategoryTheory Limits Opposite Abelian TopologicalSpace AlgebraicGeometry
universe w' v u
noncomputable section
variable {X : Scheme.{u}} (U : X.Opens)

theorem GroundTheory.Arith.SchemeCoh.overEquivalence_inverse_left (W : U.toScheme.Opens) :
    (U.overEquivalence.inverse.obj W).left = U.ι ''ᵁ W := by sorry
