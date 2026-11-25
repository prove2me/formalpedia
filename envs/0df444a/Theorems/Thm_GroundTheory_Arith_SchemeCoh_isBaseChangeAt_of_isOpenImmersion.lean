-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBaseChangeAt_of_isOpenImmersion
-- name    : GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:00.937683+00:00
-- url     : https://prove2.me/theorems/54a2efb6-0a4b-467d-b2fe-9c0cbf7f195c
-- title:
--   Scheme Coh: is Base Change At of is Open Immersion
-- statement:
--   The Scheme Coh construction uses the is Base Change At of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L103-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L103-L121

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

theorem GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isOpenImmersion (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules)
    {O : U.Opens} (hO : O ≤ j.opensRange) : IsBaseChangeAt j N O := by sorry
