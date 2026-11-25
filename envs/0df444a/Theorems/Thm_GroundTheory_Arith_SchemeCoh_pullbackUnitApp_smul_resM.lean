-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_resM
-- name    : GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_resM
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:37.222083+00:00
-- url     : https://prove2.me/theorems/a6796389-c0cb-4f64-ba80-31706e7df820
-- title:
--   Scheme Coh: pullback Unit App smul res M
-- statement:
--   The Scheme Coh construction uses the pullback Unit App smul res M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L113-L120

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_resM (j : Y ⟶ Z) (N : Z.Modules) {O V : Z.Opens} (h : V ≤ O)
    (r : ringOn Z V) (t : Γ(N, O)) :
    pullbackUnitApp j N V (r • resM ((preMod Z).obj N) h t) =
      appR j V r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
        ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t) := by sorry
