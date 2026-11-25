-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_preMod_map_homOfPreMod
-- name    : GroundTheory.Arith.SchemeCoh.preMod_map_homOfPreMod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:22.238168+00:00
-- url     : https://prove2.me/theorems/a2e45f77-da5f-4188-b6cf-37fd0a0391f0
-- title:
--   Scheme Coh: pre Mod map hom Of Pre Mod
-- statement:
--   The Scheme Coh construction uses the pre Mod map hom Of Pre Mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L77-L88

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.preMod_map_homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) :
    (preMod X).map (homOfPreMod g) = g := by sorry
