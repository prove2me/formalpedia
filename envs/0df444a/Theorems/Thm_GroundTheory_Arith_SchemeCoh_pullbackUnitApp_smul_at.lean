-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_at
-- name    : GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_at
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:11:04.790108+00:00
-- url     : https://prove2.me/theorems/cf67285b-8dfe-4a1e-9481-c5fb15a5a5b8
-- title:
--   Scheme Coh: pullback Unit App smul at
-- statement:
--   The Scheme Coh construction uses the pullback Unit App smul at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L16-L19

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

theorem GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_at (g : T ⟶ U) (N : U.Modules) (O : U.Opens) (a : Γ(U, O))
    (n : Γ(N, O)) :
    Etale.pullbackUnitApp g N O (a • n) = g.app O a • Etale.pullbackUnitApp g N O n := by sorry
