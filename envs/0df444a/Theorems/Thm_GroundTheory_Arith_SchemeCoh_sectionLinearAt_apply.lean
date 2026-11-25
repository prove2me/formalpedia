-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
-- name    : GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:05.744854+00:00
-- url     : https://prove2.me/theorems/b938230b-ddb2-43d2-807a-27c6ee78dc49
-- title:
--   Scheme Coh: section Linear At apply
-- statement:
--   The Scheme Coh construction uses the section Linear At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L27-L28

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
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
variable {W T U : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P')
    (O : X.Opens) (x : Γ(P, O)) : sectionLinearAt θ O x = θ.app O x := by sorry

attribute [defeq] GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply
