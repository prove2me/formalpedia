-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_of_pullbackUnitApp_comp
-- name    : GroundTheory.Arith.SchemeCoh.isBasisOn_of_pullbackUnitApp_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:42.595467+00:00
-- url     : https://prove2.me/theorems/084ca8be-6480-4b1b-b7f4-f81d4a51b061
-- title:
--   Scheme Coh: is Basis On of pullback Unit App comp
-- statement:
--   The Scheme Coh construction uses the is Basis On of pullback Unit App comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L173-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean#L173-L185

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

theorem GroundTheory.Arith.SchemeCoh.isBasisOn_of_pullbackUnitApp_comp {T : Scheme.{u}} (c : T ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules)
    (O : Z.Opens) (t : Γ(N, O))
    (h : IsBasisOn ((preMod T).obj
      ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N)))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (pullbackUnitApp c _ (d ⁻¹ᵁ O) (pullbackUnitApp d N O t))) :
    IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback (c ≫ d)).obj N)) ((c ≫ d) ⁻¹ᵁ O)
      (pullbackUnitApp (c ≫ d) N O t) := by sorry
