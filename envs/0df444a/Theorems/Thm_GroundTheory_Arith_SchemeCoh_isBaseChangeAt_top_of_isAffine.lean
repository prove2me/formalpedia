-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBaseChangeAt_top_of_isAffine
-- name    : GroundTheory.Arith.SchemeCoh.isBaseChangeAt_top_of_isAffine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:55.860835+00:00
-- url     : https://prove2.me/theorems/9412ca5c-f2d8-4e4e-93f8-6321b710ff8c
-- title:
--   Scheme Coh: is Base Change At top of is Affine
-- statement:
--   The Scheme Coh construction uses the is Base Change At top of is Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L207-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L207-L210

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

theorem GroundTheory.Arith.SchemeCoh.isBaseChangeAt_top_of_isAffine (h : T ⟶ U) [IsAffine T] [IsAffine U] (N : U.Modules)
    [N.IsQuasicoherent] : IsBaseChangeAt h N ⊤ := by sorry
