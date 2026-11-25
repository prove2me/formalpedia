-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_naturality
-- name    : GroundTheory.Arith.SchemeCoh.pullbackUnitApp_naturality
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:38.421038+00:00
-- url     : https://prove2.me/theorems/3444a019-a3d2-454f-b661-8211e5d2babf
-- title:
--   Scheme Coh: pullback Unit App naturality
-- statement:
--   The Scheme Coh construction uses the pullback Unit App naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L38-L46

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

theorem GroundTheory.Arith.SchemeCoh.pullbackUnitApp_naturality (f : Y ⟶ Z) {N N' : Z.Modules} (φ : N ⟶ N') (O : Z.Opens)
    (n : Γ(N, O)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ O) (pullbackUnitApp f N O n) =
      pullbackUnitApp f N' O (φ.app O n) := by sorry
