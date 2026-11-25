-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitIso_hom_one
-- name    : GroundTheory.Arith.SchemeCoh.pullbackUnitIso_hom_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:42:58.056354+00:00
-- url     : https://prove2.me/theorems/d1dc8e26-6074-4c71-a8df-8ec1eaee0ea2
-- title:
--   Scheme Coh: pullback Unit Iso hom one
-- statement:
--   The Scheme Coh construction uses the pullback Unit Iso hom one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L50-L58

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
set_option backward.isDefEq.respectTransparency.types false

theorem GroundTheory.Arith.SchemeCoh.pullbackUnitIso_hom_one (f : Y ⟶ Z) :
    (pullbackUnitIso f).hom.app ⊤
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) = unitOne Y ⊤ := by sorry
