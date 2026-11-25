-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_pullbackUnitApp
-- name    : GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:23.449083+00:00
-- url     : https://prove2.me/theorems/ff0843ae-d9fd-471f-98f0-f0712f527801
-- title:
--   Scheme Coh: is Basis On pullback Unit App
-- statement:
--   The Scheme Coh construction uses the is Basis On pullback Unit App property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L187-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L187-L200

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

theorem GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp (f : Y ⟶ Z) {N : Z.Modules} {W : Z.Opens} {t : Γ(N, W)}
    (ht : IsBasisOn ((preMod Z).obj N) W t) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj N)) (f ⁻¹ᵁ W)
      (pullbackUnitApp f N W t) := by sorry
